module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalHJ
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSp44Defs

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b

section Quot

variable {Q : Type} [Group Q] [Finite Q]

local notation "O" => standardComponentOddCore Q
local notation "π" => QuotientGroup.mk' (standardComponentOddCore Q)

theorem mem_centralizer_of_disp_mem {M : Subgroup Q} (hOM : O ≤ centralizer (M : Set Q))
    (hM : IsSimpleGroup ↥M) (hev : Even (Nat.card M)) {f : Q}
    (hf : ∀ m ∈ M, m⁻¹ * (f * m * f⁻¹) ∈ O) : f ∈ centralizer (M : Set Q) := by
  let δ : ↥M →* ↥O :=
    { toFun := fun m => ⟨(m : Q)⁻¹ * (f * m * f⁻¹), hf m m.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp only [Subgroup.coe_mul, MulMemClass.mk_mul_mk]
        have h1 := mem_centralizer_iff.mp (hOM (hf a a.2)) b b.2
        have key : (b : Q)⁻¹ * ((a : Q)⁻¹ * (f * a * f⁻¹)) =
            ((a : Q)⁻¹ * (f * a * f⁻¹)) * (b : Q)⁻¹ := by
          calc (b : Q)⁻¹ * ((a : Q)⁻¹ * (f * a * f⁻¹))
              = (b : Q)⁻¹ * (((a : Q)⁻¹ * (f * a * f⁻¹)) * b) * (b : Q)⁻¹ := by group
            _ = (b : Q)⁻¹ * (b * ((a : Q)⁻¹ * (f * a * f⁻¹))) * (b : Q)⁻¹ := by rw [h1]
            _ = ((a : Q)⁻¹ * (f * a * f⁻¹)) * (b : Q)⁻¹ := by group
        calc ((a : Q) * b)⁻¹ * (f * (a * b) * f⁻¹)
            = (b : Q)⁻¹ * ((a : Q)⁻¹ * (f * a * f⁻¹)) * (f * b * f⁻¹) := by group
          _ = ((a : Q)⁻¹ * (f * a * f⁻¹)) * (b : Q)⁻¹ * (f * b * f⁻¹) := by rw [key]
          _ = (a : Q)⁻¹ * (f * a * f⁻¹) * ((b : Q)⁻¹ * (f * b * f⁻¹)) := by group }
  have := hM
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal δ.ker with h | h
  · exfalso
    have hinj : Function.Injective δ := (MonoidHom.ker_eq_bot_iff δ).mp h
    have hdvd : Nat.card ↥M ∣ Nat.card ↥O := Subgroup.card_dvd_of_injective δ hinj
    exact (Nat.not_even_iff_odd.mpr ((odd_card_standardComponentOddCore (G := Q)).of_dvd_nat hdvd))
      hev
  · rw [mem_centralizer_iff]
    intro m hm
    have hmk : (⟨m, hm⟩ : ↥M) ∈ δ.ker := by rw [h]; exact mem_top _
    have h1 : (m : Q)⁻¹ * (f * m * f⁻¹) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hmk)
    have h2 : f * m * f⁻¹ = m := by
      calc f * m * f⁻¹ = m * ((m : Q)⁻¹ * (f * m * f⁻¹)) := by group
        _ = m := by rw [h1, mul_one]
    calc m * f = f * m * f⁻¹ * f := by rw [h2]
      _ = f * m := by group

omit [Finite Q] in
theorem mem_rightConjugate_inv_iff (R : Subgroup Q) (f x : Q) :
    x ∈ rightConjugate R f⁻¹ ↔ f⁻¹ * x * f ∈ R := by
  rw [mem_rightConjugate_iff, inv_inv]

theorem isSylowOf_comap_map {R P : Subgroup Q} (hR : IsPGroup 2 R) (hP : IsPGroup 2 P)
    (hPX : P ≤ (R.map π).comap π) (hPR : P.map π = R.map π) :
    IsSylowOf 2 P ((R.map π).comap π) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := (R.map π).comap π with hX
  obtain ⟨S, hS, hPS⟩ : ∃ S : Subgroup Q, IsSylowOf 2 S X ∧ P ≤ S := by
    have hP' : IsPGroup 2 (P.subgroupOf X) := hP.comap_subtype
    obtain ⟨T, hT⟩ := hP'.exists_le_sylow
    refine ⟨(T : Subgroup X).map X.subtype, ⟨T, rfl⟩, fun x hx => ?_⟩
    exact ⟨⟨x, hPX hx⟩, hT (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hS2 := hS.isPGroup
  have hXmap : X.map π = R.map π :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O) _
  have hSmap : S.map π = R.map π := by
    have h1 := RankTwoSporadic.IsSylowOf.map hS π
    rw [hXmap] at h1
    exact (h1.eq_of_le h1.le le_rfl (hR.map π)).symm
  have hSP : S = P := by
    refine (Subgroup.eq_of_le_of_card_ge hPS ?_).symm
    rw [← card_map_mk'_of_two hS2, ← card_map_mk'_of_two hP, hSmap, hPR]
  rw [← hSP]
  exact hS

theorem exists_mul_mem_normalizer_of_mk' {R : Subgroup Q} (hR : IsPGroup 2 R) {f : Q}
    (hf : π f ∈ normalizer ((R.map π : Subgroup (Q ⧸ O)) : Set (Q ⧸ O))) :
    ∃ o ∈ O, o * f ∈ normalizer (R : Set Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := (R.map π).comap π with hX
  set R' := rightConjugate R f⁻¹ with hR'
  have hRX : R ≤ X := fun r hr => mem_comap.mpr (mem_map_of_mem _ hr)
  have hR'map : R'.map π = R.map π := by
    ext z
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective O z
    constructor
    · rintro ⟨v, hv, hvw⟩
      have hv' : f⁻¹ * v * f ∈ R := (mem_rightConjugate_inv_iff R f v).mp hv
      rw [← hvw, show v = f * (f⁻¹ * v * f) * f⁻¹ by group, map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp hf _).mp (mem_map_of_mem _ hv')
    · intro hz
      have h1 : π f⁻¹ * π w * (π f⁻¹)⁻¹ ∈ R.map π := by
        have := (mem_normalizer_iff.mp (inv_mem hf) (π w)).mp hz
        simpa [map_inv] using this
      obtain ⟨r, hr, hrw⟩ := h1
      refine ⟨f * r * f⁻¹, (mem_rightConjugate_inv_iff R f _).mpr (by simpa [mul_assoc] using hr),
        ?_⟩
      rw [map_mul, map_mul, map_inv, hrw, map_inv]
      group
  have hR'X : R' ≤ X := by
    intro z hz
    rw [mem_comap, ← hR'map]
    exact mem_map_of_mem _ hz
  have hR'2 : IsPGroup 2 R' := hR.map _
  have hSylR : IsSylowOf 2 R X := isSylowOf_comap_map hR hR hRX rfl
  have hSylR' : IsSylowOf 2 R' X := isSylowOf_comap_map hR hR'2 hR'X hR'map
  obtain ⟨g, hgX, hg⟩ := hSylR.exists_mem_conj hSylR'
  have hXeq : X = R ⊔ O := by rw [hX, comap_map_eq, QuotientGroup.ker_mk']
  rw [hXeq] at hgX
  obtain ⟨r, hr, o, ho, rfl⟩ := mem_sup_of_normal_right.mp hgX
  refine ⟨(r * o * r⁻¹)⁻¹,
    inv_mem ((inferInstance : (standardComponentOddCore Q).Normal).conj_mem o ho r), ?_⟩
  rw [mem_normalizer_iff]
  intro w
  have h1 := hg (f * w * f⁻¹)
  rw [mem_rightConjugate_inv_iff, show f⁻¹ * (f * w * f⁻¹) * f = w by group] at h1
  rw [h1]
  have e : (r * o)⁻¹ * (f * w * f⁻¹) * (r * o) =
      r⁻¹ * ((r * o * r⁻¹)⁻¹ * f * w * ((r * o * r⁻¹)⁻¹ * f)⁻¹) * r := by group
  rw [e]
  constructor
  · intro h
    have := mul_mem (mul_mem hr h) (inv_mem hr)
    simpa [mul_assoc] using this
  · intro h
    exact mul_mem (mul_mem (inv_mem hr) h) hr

omit [Finite Q] in
theorem isSimpleGroup_of_isQuasisimple {M : Subgroup Q} (hq : CFSG.Open.IsQuasisimple ↥M)
    (hZ : center ↥M = ⊥) : IsSimpleGroup ↥M := by
  have := hq.2
  have e : (↥M ⧸ center ↥M) ≃* ↥M :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup

theorem commutator_subgroupOf_eq {X : Type*} [Group X] {H K : Subgroup X} (hHK : H ≤ K)
    (hH : ⁅H, H⁆ = H) : ⁅H.subgroupOf K, H.subgroupOf K⁆ = H.subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hHK, hH]

omit [Finite Q] in
theorem orderOf_mk'_of_inf {M : Subgroup Q} (hMO : M ⊓ O = ⊥) {m : Q} (hm : m ∈ M) :
    orderOf (π m) = orderOf m := by
  have h := orderOf_injective ((QuotientGroup.mk' O).comp M.subtype)
    (fun a b hab => Subtype.ext (mk'_injOn_of_inf hMO a.2 b.2 hab)) ⟨m, hm⟩
  rw [Subgroup.orderOf_mk] at h
  simpa using h

omit [Finite Q] in
theorem mk'_eq_one_of_mem {o : Q} (ho : o ∈ O) : π o = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact ho

theorem mem_centralizer_of_mem_oddCore {P : Subgroup Q}
    (hP : IsPGroup 2 P) {f : Q} (hfO : f ∈ O)
    (hfP : f ∈ normalizer (P : Set Q)) : f ∈ centralizer (P : Set Q) := by
  have hbot := inf_eq_bot_of_two hP (odd_card_standardComponentOddCore (G := Q))
  rw [mem_centralizer_iff]
  intro p hp
  have h1 : f * p * f⁻¹ * p⁻¹ ∈ P :=
    mul_mem ((mem_normalizer_iff.mp hfP p).mp hp) (inv_mem hp)
  have h2 : f * p * f⁻¹ * p⁻¹ ∈ O := by
    have h3 : p * f⁻¹ * p⁻¹ ∈ O :=
      (inferInstance : (O).Normal).conj_mem _ (inv_mem hfO) p
    have := mul_mem hfO h3
    simpa [mul_assoc] using this
  have h4 : f * p * f⁻¹ * p⁻¹ ∈ P ⊓ O := mem_inf.mpr ⟨h1, h2⟩
  rw [hbot, mem_bot] at h4
  have h5 : f * p * f⁻¹ = p := by
    calc f * p * f⁻¹ = f * p * f⁻¹ * p⁻¹ * p := by group
      _ = p := by rw [h4, one_mul]
  calc p * f = f * p * f⁻¹ * f := by rw [h5]
    _ = f * p := by group


theorem j2A4_apply (hJ : J2A4Facts) {M R : Subgroup Q} (hH : RankTwoHyp Q M)
    (hX : NativeSporadic.IsSporadic (rankTwoX (M.map π)) .J2) (hR : IsElemAbelian 2 R)
    (hR4 : 4 ≤ Nat.card R) (hRM : R ≤ centralizer (M : Set Q)) (hZM : center ↥M = ⊥)
    (hMp : ⁅M, M⁆ = M) (hM60 : Nat.card M = 60) {w : Q} (hwM : w ∈ M) (hw5 : orderOf w = 5) :
    (∀ x ∈ (M.map π).subgroupOf (rankTwoX (M.map π)), orderOf x = 5 →
      ∃ H : Subgroup ↥(rankTwoX (M.map π)),
        H ≤ ⁅centralizer ({x} : Set ↥(rankTwoX (M.map π))),
          centralizer ({x} : Set ↥(rankTwoX (M.map π)))⁆ ∧ Nat.card H = 60 ∧ IsSimpleGroup ↥H) ∧
    (∀ z ∈ (M.map π).subgroupOf (rankTwoX (M.map π)), orderOf z = 3 →
      ∀ β : MulAut ↥(rankTwoX (M.map π)), (∃ k : ℕ, β ^ 5 ^ k = 1) → β z = z → β = 1) ∧
    (∃ f ∈ centralizer (((M.map π).subgroupOf (rankTwoX (M.map π)) :
        Subgroup ↥(rankTwoX (M.map π))) : Set ↥(rankTwoX (M.map π))), orderOf f = 3 ∧
      f ∈ normalizer (((R.map π).subgroupOf (rankTwoX (M.map π)) :
        Subgroup ↥(rankTwoX (M.map π))) : Set ↥(rankTwoX (M.map π))) ∧
      f ∉ centralizer (((R.map π).subgroupOf (rankTwoX (M.map π)) :
        Subgroup ↥(rankTwoX (M.map π))) : Set ↥(rankTwoX (M.map π)))) := by
  set X := rankTwoX (M.map π) with hXdef
  have hMO := inf_oddCore_eq_bot hH hZM
  have hMX : M.map π ≤ X := le_normalClosure
  have hRX := map_le_rankTwoX hH hX hR hRM hZM hwM hw5
  have hR2 := isPGroup_of_isElemAbelian hR
  have hcardV : Nat.card ((R.map π).subgroupOf X) = Nat.card R := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRX).toEquiv, card_map_mk'_of_two hR2]
  have hcardΛ : Nat.card ((M.map π).subgroupOf X) = 60 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hMX).toEquiv, card_map_mk'_of_inf hMO, hM60]
  have hΛp : ⁅(M.map π).subgroupOf X, (M.map π).subgroupOf X⁆ = (M.map π).subgroupOf X := by
    refine commutator_subgroupOf_eq hMX ?_
    rw [← Subgroup.map_commutator, hMp]
  have hVΛ : (R.map π).subgroupOf X ≤ centralizer (((M.map π).subgroupOf X : Subgroup ↥X) :
      Set ↥X) := by
    intro v hv
    rw [mem_centralizer_iff]
    intro l hl
    obtain ⟨r, hr, hrv⟩ := mem_subgroupOf.mp hv
    obtain ⟨m, hm, hml⟩ := mem_subgroupOf.mp hl
    apply Subtype.ext
    change (l : Q ⧸ O) * v = v * l
    rw [← hrv, ← hml, ← map_mul, ← map_mul, (mem_centralizer_iff.mp (hRM hr) m hm)]
  exact hJ ↥X hX ((R.map π).subgroupOf X) ((M.map π).subgroupOf X)
    (hR2.map _ |>.comap_subtype) (hcardV ▸ hR4) hcardΛ hΛp hVΛ

theorem exists_three_of_j2A4 (hJ : J2A4Facts) {M R : Subgroup Q} (hH : RankTwoHyp Q M)
    (hX : NativeSporadic.IsSporadic (rankTwoX (M.map π)) .J2) (hR : IsElemAbelian 2 R)
    (hR4 : 4 ≤ Nat.card R) (hRM : R ≤ centralizer (M : Set Q)) (hZM : center ↥M = ⊥)
    (hMp : ⁅M, M⁆ = M) (hM60 : Nat.card M = 60) {w : Q} (hwM : w ∈ M) (hw5 : orderOf w = 5) :
    ∃ f : Q, f ∈ centralizer (M : Set Q) ∧ f ∈ normalizer (R : Set Q) ∧
      (∃ k : ℕ, f ^ 3 ^ k = 1) ∧ f ∉ centralizer (R : Set Q) := by
  have hMX : M.map π ≤ rankTwoX (M.map π) := le_normalClosure
  have hRX := map_le_rankTwoX hH hX hR hRM hZM hwM hw5
  obtain ⟨-, -, fb, hfΛ, hf3, hfV, hfV'⟩ :=
    j2A4_apply hJ hH hX hR hR4 hRM hZM hMp hM60 hwM hw5
  have hf1M : ∀ m ∈ M, π m * (fb : Q ⧸ O) = (fb : Q ⧸ O) * π m := by
    intro m hm
    have h := mem_centralizer_iff.mp hfΛ ⟨π m, hMX (mem_map_of_mem _ hm)⟩
      (mem_subgroupOf.mpr (mem_map_of_mem _ hm))
    simpa using congrArg Subtype.val h
  have hf1R : (fb : Q ⧸ O) ∈ normalizer ((R.map π : Subgroup (Q ⧸ O)) : Set (Q ⧸ O)) := by
    rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have h := (mem_normalizer_iff.mp hfV ⟨z, hRX hz⟩).mp (mem_subgroupOf.mpr hz)
      simpa using mem_subgroupOf.mp h
    · intro hz
      have hzX : z ∈ rankTwoX (M.map π) := by
        have h1 : (fb : Q ⧸ O) * z * (fb : Q ⧸ O)⁻¹ ∈ rankTwoX (M.map π) := hRX hz
        have h2 : (fb : Q ⧸ O)⁻¹ * ((fb : Q ⧸ O) * z * (fb : Q ⧸ O)⁻¹) * (fb : Q ⧸ O) ∈
            rankTwoX (M.map π) := mul_mem (mul_mem (inv_mem fb.2) h1) fb.2
        simpa [mul_assoc] using h2
      have h := (mem_normalizer_iff.mp hfV ⟨z, hzX⟩).mpr (mem_subgroupOf.mpr (by simpa using hz))
      exact mem_subgroupOf.mp h
  obtain ⟨f₀, hf₀⟩ := QuotientGroup.mk'_surjective O (fb : Q ⧸ O)
  rw [← hf₀] at hf1R
  obtain ⟨o, ho, hof⟩ := exists_mul_mem_normalizer_of_mk' (isPGroup_of_isElemAbelian hR) hf1R
  have hπf₂ : π (o * f₀) = (fb : Q ⧸ O) := by rw [map_mul, mk'_eq_one_of_mem ho, one_mul, hf₀]
  have hf₂M : o * f₀ ∈ centralizer (M : Set Q) := by
    refine mem_centralizer_of_disp_mem (oddCore_le_of_rankTwoHyp hH)
      (isSimpleGroup_of_isQuasisimple hH.standard.1 hZM) (by rw [hM60]; decide) fun m hm => ?_
    rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      hπf₂]
    have h := hf1M m hm
    calc (π m)⁻¹ * ((fb : Q ⧸ O) * π m * (fb : Q ⧸ O)⁻¹)
        = (π m)⁻¹ * (π m * (fb : Q ⧸ O) * (fb : Q ⧸ O)⁻¹) := by rw [h]
      _ = 1 := by group
  obtain ⟨a, b, hb3, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (o * f₀)).ne' 3
    (by norm_num)
  refine ⟨(o * f₀) ^ b, Subgroup.pow_mem _ hf₂M b, Subgroup.pow_mem _ hof b, ⟨a, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
  · intro hc
    apply hfV'
    have hcop : Nat.Coprime b (orderOf fb) := by
      rw [hf3]
      exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hb3)
    obtain ⟨c, hc'⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hc']
    refine Subgroup.pow_mem _ ?_ c
    rw [mem_centralizer_iff]
    intro v hv
    obtain ⟨r, hr, hrv⟩ := mem_subgroupOf.mp hv
    apply Subtype.ext
    have h2 := congrArg π (mem_centralizer_iff.mp hc r hr)
    rw [map_mul, map_mul, map_pow, hπf₂] at h2
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
    rw [← hrv]
    exact h2

theorem exists_five_of_j2A4 (hJ : J2A4Facts) {M R : Subgroup Q} (hH : RankTwoHyp Q M)
    (hX : NativeSporadic.IsSporadic (rankTwoX (M.map π)) .J2) (hR : IsElemAbelian 2 R)
    (hR4 : 4 ≤ Nat.card R) (hRM : R ≤ centralizer (M : Set Q)) (hZM : center ↥M = ⊥)
    (hMp : ⁅M, M⁆ = M) (hM60 : Nat.card M = 60) {x : Q} (hxM : x ∈ M) (hx5 : orderOf x = 5) :
    ∃ S : Subgroup Q, S ≤ centralizer ({x} : Set Q) ∧ ∀ N : Subgroup Q, N ≤ S →
      S ≤ normalizer (N : Set Q) → Odd (Nat.card N) →
        ∃ h ∈ S, (∃ k : ℕ, h ^ 5 ^ k = 1) ∧ h ∉ N := by
  have hMO := inf_oddCore_eq_bot hH hZM
  have hMX : M.map π ≤ rankTwoX (M.map π) := le_normalClosure
  have hxX : π x ∈ rankTwoX (M.map π) := hMX (mem_map_of_mem _ hxM)
  obtain ⟨ha, -, -⟩ := j2A4_apply hJ hH hX hR hR4 hRM hZM hMp hM60 hxM hx5
  obtain ⟨Hb, hHb, hHb60, hHbs⟩ := ha ⟨π x, hxX⟩ (mem_subgroupOf.mpr (mem_map_of_mem _ hxM))
    (by rw [Subgroup.orderOf_mk, orderOf_mk'_of_inf hMO hxM, hx5])
  set H' := Hb.map (rankTwoX (M.map π)).subtype with hH'
  have hK : (centralizer ({(⟨π x, hxX⟩ : ↥(rankTwoX (M.map π)))} : Set ↥(rankTwoX (M.map π)))).map
      (rankTwoX (M.map π)).subtype = rankTwoX (M.map π) ⊓ centralizer ({π x} : Set (Q ⧸ O)) := by
    ext z
    rw [mem_map, mem_inf]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [mem_centralizer_singleton_iff] at hw
      exact ⟨w.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hw)⟩
    · rintro ⟨hzX, hzC⟩
      exact ⟨⟨z, hzX⟩, mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hzC)), rfl⟩
  have hH'le : H' ≤ ⁅rankTwoX (M.map π) ⊓ centralizer ({π x} : Set (Q ⧸ O)),
      rankTwoX (M.map π) ⊓ centralizer ({π x} : Set (Q ⧸ O))⁆ := by
    rw [← hK, ← map_commutator, hH']
    exact map_mono hHb
  set S := centralizer ({x} : Set Q) ⊓ H'.comap π with hS
  have hSlift : ∀ c ∈ H', ∃ c' ∈ S, π c' = c := by
    intro c hc
    obtain ⟨c', hc'x, hc'c⟩ := commutator_lift hH hxM (hH'le hc)
    exact ⟨c', mem_inf.mpr ⟨hc'x, mem_comap.mpr (hc'c ▸ hc)⟩, hc'c⟩
  have hH'card : Nat.card H' = 60 := by
    rw [hH', card_map_of_injective (rankTwoX (M.map π)).subtype_injective, hHb60]
  have hH's : IsSimpleGroup ↥H' := by
    have := hHbs
    exact (Hb.equivMapOfInjective _ (rankTwoX (M.map π)).subtype_injective).symm.isSimpleGroup
  refine ⟨S, inf_le_left, fun N hNS hSN hNodd => ?_⟩
  have hNH : N.map π ≤ H' := by
    rintro _ ⟨n, hn, rfl⟩
    exact mem_comap.mp (mem_inf.mp (hNS hn)).2
  have hNn : ((N.map π).subgroupOf H').Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hNH]
    intro c hc
    obtain ⟨c', hc'S, rfl⟩ := hSlift c hc
    rw [mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨c' * n * c'⁻¹, (mem_normalizer_iff.mp (hSN hc'S) n).mp hn, by simp⟩
    · rintro ⟨n, hn, hnz⟩
      refine ⟨c'⁻¹ * n * c', ?_, ?_⟩
      · have := (mem_normalizer_iff.mp (hSN (inv_mem hc'S)) n).mp hn
        simpa [mul_assoc] using this
      · rw [map_mul, map_mul, map_inv, hnz]
        group
  have hNbot : N.map π = ⊥ := by
    have := hH's
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.map π).subgroupOf H') with h | h
    · rw [eq_bot_iff]
      intro z hz
      have hz' : (⟨z, hNH hz⟩ : ↥H') ∈ (N.map π).subgroupOf H' := mem_subgroupOf.mpr hz
      rw [h, mem_bot] at hz'
      exact mem_bot.mpr (congrArg Subtype.val hz')
    · exfalso
      have heq : N.map π = H' := by
        refine le_antisymm hNH fun z hz => ?_
        have hz' : (⟨z, hz⟩ : ↥H') ∈ (N.map π).subgroupOf H' := by rw [h]; exact mem_top _
        exact mem_subgroupOf.mp hz'
      have hdvd : Nat.card (N.map π) ∣ Nat.card N := Subgroup.card_map_dvd _ _
      rw [heq, hH'card] at hdvd
      have := hNodd.of_dvd_nat hdvd
      norm_num at this
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨c, hc5⟩ := exists_prime_orderOf_dvd_card' (G := ↥H') 5 (by rw [hH'card]; norm_num)
  obtain ⟨c', hc'S, hc'c⟩ := hSlift c c.2
  obtain ⟨a, b, hb5, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c').ne' 5
    (by norm_num)
  refine ⟨c' ^ b, Subgroup.pow_mem _ hc'S b, ⟨a, ?_⟩, fun hN => ?_⟩
  · rw [← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
  · have h1 : π (c' ^ b) = 1 := by
      have : π (c' ^ b) ∈ N.map π := mem_map_of_mem _ hN
      rwa [hNbot, mem_bot] at this
    rw [map_pow, hc'c] at h1
    have h2 : orderOf (c : Q ⧸ O) ∣ b := orderOf_dvd_of_pow_eq_one h1
    rw [Subgroup.orderOf_coe, hc5] at h2
    exact hb5 h2

theorem mk'_eq_one_of_j2A4 (hJ : J2A4Facts) {M R : Subgroup Q} (hH : RankTwoHyp Q M)
    (hX : NativeSporadic.IsSporadic (rankTwoX (M.map π)) .J2) (hR : IsElemAbelian 2 R)
    (hR4 : 4 ≤ Nat.card R) (hRM : R ≤ centralizer (M : Set Q)) (hZM : center ↥M = ⊥)
    (hMp : ⁅M, M⁆ = M) (hM60 : Nat.card M = 60) {w : Q} (hwM : w ∈ M) (hw5 : orderOf w = 5)
    {z : Q} (hzM : z ∈ M) (hz3 : orderOf z = 3) {t : Q} (ht5 : ∃ k : ℕ, t ^ 5 ^ k = 1)
    (htz : t * z = z * t) : π t = 1 := by
  have hMO := inf_oddCore_eq_bot hH hZM
  have hMX : M.map π ≤ rankTwoX (M.map π) := le_normalClosure
  have hXn : (rankTwoX (M.map π)).Normal := normalClosure_normal
  obtain ⟨-, hc, -⟩ := j2A4_apply hJ hH hX hR hR4 hRM hZM hMp hM60 hwM hw5
  have hzX : π z ∈ rankTwoX (M.map π) := hMX (mem_map_of_mem _ hzM)
  obtain ⟨k, hk⟩ := ht5
  have hβ := hc ⟨π z, hzX⟩ (mem_subgroupOf.mpr (mem_map_of_mem _ hzM))
    (by rw [Subgroup.orderOf_mk, orderOf_mk'_of_inf hMO hzM, hz3]) (MulAut.conjNormal (π t))
    ⟨k, by rw [← map_pow, ← map_pow, hk, map_one, map_one]⟩
    (Subtype.ext (by
      rw [MulAut.conjNormal_apply]
      change π t * π z * (π t)⁻¹ = π z
      rw [← map_mul, htz, map_mul, mul_inv_cancel_right]))
  have hC : π t ∈ centralizer (rankTwoX (M.map π) : Set (Q ⧸ O)) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun β : MulAut ↥(rankTwoX (M.map π)) => ((β ⟨y, hy⟩ :
      ↥(rankTwoX (M.map π))) : Q ⧸ O)) hβ
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
    calc y * π t = π t * y * (π t)⁻¹ * π t := by rw [h]
      _ = π t * y := by group
  rw [centralizer_rankTwoX_eq_bot hH, mem_bot] at hC
  exact hC

theorem mk'_eq_one_of_m12 (hM : M12AutThreeFive) {M : Subgroup Q} (hH : RankTwoHyp Q M)
    (hX : NativeSporadic.IsSporadic (rankTwoX (M.map π)) .M12) (hZM : center ↥M = ⊥) {x : Q}
    (hxM : x ∈ M) (hx5 : orderOf x = 5) {t : Q} (ht3 : ∃ k : ℕ, t ^ 3 ^ k = 1)
    (htx : t * x = x * t) : π t = 1 := by
  have hMO := inf_oddCore_eq_bot hH hZM
  have hMX : M.map π ≤ rankTwoX (M.map π) := le_normalClosure
  have hXn : (rankTwoX (M.map π)).Normal := normalClosure_normal
  have hxX : π x ∈ rankTwoX (M.map π) := hMX (mem_map_of_mem _ hxM)
  obtain ⟨k, hk⟩ := ht3
  have hβ := hM ↥(rankTwoX (M.map π)) hX (MulAut.conjNormal (π t))
    ⟨k, by rw [← map_pow, ← map_pow, hk, map_one, map_one]⟩ ⟨π x, hxX⟩
    (by rw [Subgroup.orderOf_mk, orderOf_mk'_of_inf hMO hxM, hx5])
    (Subtype.ext (by
      rw [MulAut.conjNormal_apply]
      change π t * π x * (π t)⁻¹ = π x
      rw [← map_mul, htx, map_mul, mul_inv_cancel_right]))
  have hC : π t ∈ centralizer (rankTwoX (M.map π) : Set (Q ⧸ O)) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun β : MulAut ↥(rankTwoX (M.map π)) => ((β ⟨y, hy⟩ :
      ↥(rankTwoX (M.map π))) : Q ⧸ O)) hβ
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
    calc y * π t = π t * y * (π t)⁻¹ * π t := by rw [h]
      _ = π t * y := by group
  rw [centralizer_rankTwoX_eq_bot hH, mem_bot] at hC
  exact hC

end Quot

end CFSG.ComponentClassification.RankTwoClassical
