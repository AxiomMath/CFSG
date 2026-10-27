module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBInputs
public import CFSG.LocalAnalysis.ComponentClassification.TBLitQuotSL
public import CFSG.LieType.Steinberg.CentralExt.Families

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open CFSG Subgroup CFSG.ComponentClassification.TBLit
open scoped MatrixGroups IsMulCommutative

theorem false_of_central_sq {G L : Type} [Group G] [Finite G] [Group L] {α : G →* L}
    (hα : Function.Surjective α) {g z : G} (hαg : α g = 1)
    (hker : ∀ x, α x = 1 → x = 1 ∨ x = g) (hg : g ∈ center G) (hg2 : orderOf g = 2)
    (hz : z ∈ center G) (hzg : z ^ 2 = g) {Q : Subgroup L} (hzQ : α z ∈ Q) {F : Type}
    [Field F] [Finite F] (hF : ringChar F ≠ 2) (e : Q ⧸ pPrimeCore 2 Q ≃* SL(2, F)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite L := Finite.of_surjective α hα
  set Qt : Subgroup G := Q.comap α with hQt
  have hgQt : g ∈ Qt := by rw [hQt, mem_comap, hαg]; exact one_mem Q
  have hzQt : z ∈ Qt := hzQ
  set α' : Qt →* Q := (α.comp Qt.subtype).codRestrict Q (fun x => x.2) with hα'
  have hα's : Function.Surjective α' := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hα y
    exact ⟨⟨x, hy⟩, rfl⟩
  set π₀ : Qt →* SL(2, F) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (pPrimeCore 2 Q)).comp α') with hπ₀def
  have hπ₀ : Function.Surjective π₀ :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp hα's)
  set g' : Qt := ⟨g, hgQt⟩ with hg'
  set z' : Qt := ⟨z, hzQt⟩ with hz'
  have hg'c : g' ∈ center Qt := mem_center_iff.2 fun x => Subtype.ext (mem_center_iff.1 hg x)
  have hz'c : z' ∈ center Qt := mem_center_iff.2 fun x => Subtype.ext (mem_center_iff.1 hz x)
  have hg'2 : orderOf g' = 2 := by
    rw [← orderOf_injective Qt.subtype Subtype.val_injective g']
    exact hg2
  have hg'g' : g' * g' = 1 := by rw [← pow_two, ← hg'2, pow_orderOf_eq_one]
  have hz'g' : z' ^ 2 = g' := Subtype.ext (by rw [Subgroup.coe_pow]; exact hzg)
  set P := π₀.ker with hP
  have hPO : ∀ x : Qt, x ∈ P → α' x ∈ pPrimeCore 2 Q := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : QuotientGroup.mk' (pPrimeCore 2 Q) (α' x) = 1 :=
      e.injective (by rw [map_one]; exact hx)
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hα'g : α' g' = 1 := Subtype.ext hαg
  have hg'P : g' ∈ P := by
    rw [hP, MonoidHom.mem_ker, hπ₀def, MonoidHom.comp_apply, MonoidHom.comp_apply, hα'g, map_one,
      map_one]
  set gP : P := ⟨g', hg'P⟩ with hgP
  set H : Subgroup P := zpowers gP with hH
  have hgPc : gP ∈ center P := mem_center_iff.2 fun x => Subtype.ext (mem_center_iff.1 hg'c x)
  have hHc : H ≤ center P := by rw [hH, zpowers_le]; exact hgPc
  have hgP2 : gP ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact hg'g')
  set f : P →* Q := α'.comp P.subtype with hf
  have hfker : f.ker = H := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : α (x : G) = 1 := congrArg Subtype.val hx
      rcases hker _ h1 with h | h
      · have : x = 1 := Subtype.ext (Subtype.ext h)
        rw [this]
        exact one_mem _
      · have : x = gP := Subtype.ext (Subtype.ext h)
        rw [this]
        exact mem_zpowers _
    · intro hx
      rcases eq_one_or_eq_of_mem_zpowers hgP2 hx with rfl | rfl
      · exact map_one f
      · exact hα'g
  have hm : ¬ 2 ∣ H.index := by
    rw [← hfker, Subgroup.index_ker]
    have hle : f.range ≤ pPrimeCore 2 Q := by
      rintro _ ⟨x, rfl⟩
      exact hPO x x.2
    have hdvd : Nat.card f.range ∣ Nat.card (pPrimeCore 2 Q) := Subgroup.card_dvd_of_le hle
    have hcop := pPrimeCore_coprime_card (p := 2) (G := Q)
    intro h2
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hcop (h2.trans hdvd)
  set m := H.index with hmdef
  set τ : P →* center P := MonoidHom.transfer (Subgroup.inclusion hHc) with hτ
  have hkey : ∀ x : P, ∀ (k : ℕ) (g₀ : P), g₀⁻¹ * x ^ k * g₀ ∈ H →
      g₀⁻¹ * x ^ k * g₀ = x ^ k := by
    intro x k g₀ hk
    have hc := mem_center_iff.1 (hHc hk) g₀
    calc g₀⁻¹ * x ^ k * g₀ = g₀⁻¹ * x ^ k * g₀ * g₀ * g₀⁻¹ := by group
      _ = g₀ * (g₀⁻¹ * x ^ k * g₀) * g₀⁻¹ := by rw [← hc]
      _ = x ^ k := by group
  have hτx : ∀ x : P, τ x = 1 ↔ x ^ m = 1 := by
    intro x
    rw [hτ, MonoidHom.transfer_eq_pow _ x (hkey x)]
    constructor
    · intro h1
      have h2 := congrArg (fun y : center P => (y : P)) h1
      exact h2
    · intro h1
      exact Subtype.ext h1
  have hpowH : ∀ x : P, x ^ m = 1 ∨ x ^ m = gP := fun x =>
    eq_one_or_eq_of_mem_zpowers hgP2 (MonoidHom.transfer_eq_pow_aux x (hkey x))
  have hmodd : Odd m := Nat.odd_iff.2 (by omega)
  set H'' : Subgroup Qt := τ.ker.map P.subtype with hH''
  have hmemH'' : ∀ x : Qt, x ∈ P → x ^ m = 1 → x ∈ H'' := by
    intro x hx hxm
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, hτx]
    exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hxm)
  have hH''P : ∀ x ∈ H'', x ∈ P ∧ x ^ m = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, hτx] at hy
    have := congrArg Subtype.val hy
    rwa [Subgroup.coe_pow] at this
  have hH''n : H''.Normal := by
    refine ⟨fun x hx q => ?_⟩
    obtain ⟨hxP, hxm⟩ := hH''P x hx
    have hPn : P.Normal := MonoidHom.normal_ker π₀
    refine hmemH'' _ (hPn.conj_mem x hxP q) ?_
    rw [conj_pow, hxm, mul_one, mul_inv_cancel]
  have hH''c : Nat.Coprime 2 (Nat.card H'') := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro h2
    obtain ⟨⟨x, hx⟩, hxo⟩ := exists_prime_orderOf_dvd_card' (G := H'') 2 h2
    have hxm := (hH''P x hx).2
    have hxo' : orderOf x = 2 := by
      have := orderOf_injective H''.subtype Subtype.val_injective ⟨x, hx⟩
      rw [hxo] at this
      exact this
    have := orderOf_dvd_of_pow_eq_one hxm
    rw [hxo'] at this
    exact hm this
  have hH''O : H'' ≤ pPrimeCore 2 Qt := le_sSup ⟨hH''n, hH''c⟩
  have hOP : pPrimeCore 2 Qt ≤ π₀.ker := by
    intro x hx
    have h1 : α' x ∈ pPrimeCore 2 Q := map_pPrimeCore_le α' hα's ⟨x, hx, rfl⟩
    have h1' : QuotientGroup.mk' (pPrimeCore 2 Q) (α' x) = 1 := (QuotientGroup.eq_one_iff _).2 h1
    rw [MonoidHom.mem_ker, hπ₀def, MonoidHom.comp_apply, MonoidHom.comp_apply, h1', map_one]
  have hg'O : g' ∉ pPrimeCore 2 Qt := by
    intro h1
    have hdvd := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 Qt) h1
    rw [hg'2] at hdvd
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1
      (pPrimeCore_coprime_card (p := 2) (G := Qt)) hdvd
  set O := pPrimeCore 2 Qt with hO
  have : O.Normal := pPrimeCore_normal
  set π' : Qt ⧸ O →* SL(2, F) := QuotientGroup.lift O π₀ hOP with hπ'
  have hπ'mk : ∀ x : Qt, π' (x : Qt ⧸ O) = π₀ x := fun x => QuotientGroup.lift_mk _ _ _
  have hπ's : Function.Surjective π' := by
    intro y
    obtain ⟨x, rfl⟩ := hπ₀ y
    exact ⟨x, hπ'mk x⟩
  set gE : Qt ⧸ O := (g' : Qt ⧸ O) with hgE
  have hgE1 : gE ≠ 1 := fun h1 => hg'O ((QuotientGroup.eq_one_iff _).1 h1)
  have hgEc : gE ∈ center (Qt ⧸ O) := map_mem_center_of_surjective
    (QuotientGroup.mk'_surjective O) hg'c
  have hgE2 : gE * gE = 1 := by rw [hgE, ← QuotientGroup.mk_mul, hg'g', QuotientGroup.mk_one]
  have hkerE : ∀ k ∈ π'.ker, k = 1 ∨ k = gE := by
    intro k hk
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective k
    rw [MonoidHom.mem_ker, hπ'mk] at hk
    rcases hpowH ⟨x, hk⟩ with h | h
    · left
      have hxm : x ^ m = 1 := by
        have := congrArg Subtype.val h
        rwa [Subgroup.coe_pow] at this
      exact (QuotientGroup.eq_one_iff _).2 (hH''O (hmemH'' x hk hxm))
    · right
      have hxm : x ^ m = g' := by
        have := congrArg Subtype.val h
        rwa [Subgroup.coe_pow] at this
      have hxg : x * g' ∈ O := by
        refine hH''O (hmemH'' _ (mul_mem hk hg'P) ?_)
        have hcomm : Commute x g' := mem_center_iff.1 hg'c x
        rw [hcomm.mul_pow, hxm]
        obtain ⟨k, hk'⟩ := hmodd
        rw [hk', pow_succ, pow_mul, show g' ^ 2 = 1 by rw [pow_two, hg'g'], one_pow, one_mul,
          hg'g']
      have h1 := (QuotientGroup.eq_one_iff _).2 hxg
      rw [QuotientGroup.mk_mul] at h1
      rw [hgE]
      calc (x : Qt ⧸ O) = (x : Qt ⧸ O) * (g' : Qt ⧸ O) * (g' : Qt ⧸ O) := by
            rw [mul_assoc, ← QuotientGroup.mk_mul, hg'g', QuotientGroup.mk_one, mul_one]
        _ = (g' : Qt ⧸ O) := by rw [h1, one_mul]
  have hkerC : π'.ker ≤ center (Qt ⧸ O) := by
    intro k hk
    rcases hkerE k hk with rfl | rfl
    · exact one_mem _
    · exact hgEc
  have hker2 : IsPGroup 2 π'.ker := by
    intro k
    refine ⟨1, Subtype.ext ?_⟩
    rcases hkerE k k.2 with h | h
    · rw [Subgroup.coe_pow, h, one_pow, OneMemClass.coe_one]
    · rw [Subgroup.coe_pow, h, pow_one, pow_two, hgE2, OneMemClass.coe_one]
  obtain ⟨σ, hσ, -⟩ := CFSG.LieType.Steinberg.sl_central_two_extension_splitting 1 hF
    (π := π') hπ's hkerC hker2
  set xE : Qt ⧸ O := (z' : Qt ⧸ O) with hxE
  have hπx : π' xE ∈ center SL(2, F) := by
    rw [hxE, hπ'mk]
    exact map_mem_center_of_surjective hπ₀ hz'c
  have hπx2 : π' xE * π' xE = 1 := by
    obtain ⟨r, hr, hre⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hπx
    rw [Fintype.card_fin] at hr
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, ← hre,
      Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← pow_two, hr]
  set k := xE * (σ (π' xE))⁻¹ with hk
  have hkK : k ∈ π'.ker := by
    rw [MonoidHom.mem_ker, hk, map_mul, map_inv, hσ, mul_inv_cancel]
  have hkk : k * k = 1 := by
    rcases hkerE k hkK with h | h
    · rw [h, one_mul]
    · rw [h, hgE2]
  have hkc : k ∈ center (Qt ⧸ O) := hkerC hkK
  have hxk : xE = k * σ (π' xE) := by rw [hk, inv_mul_cancel_right]
  have hx2 : xE * xE = 1 := by
    rw [hxk]
    have hcs : σ (π' xE) * k = k * σ (π' xE) := mem_center_iff.1 hkc (σ (π' xE))
    calc k * σ (π' xE) * (k * σ (π' xE)) = k * (σ (π' xE) * k) * σ (π' xE) := by group
      _ = k * (k * σ (π' xE)) * σ (π' xE) := by rw [hcs]
      _ = (k * k) * (σ (π' xE) * σ (π' xE)) := by group
      _ = 1 := by rw [hkk, one_mul, ← map_mul, hπx2, map_one]
  apply hgE1
  rw [← hx2, hxE, hgE, ← QuotientGroup.mk_mul, ← pow_two, hz'g']

theorem eq_of_propBHypII {G : Type} [Group G] [Finite G] (hG : IsQuasisimple G) {g : G}
    (hg : g ∈ center G) (hg2 : orderOf g = 2) (hZ : ∀ z ∈ center G, z ^ 2 = 1 ∨ z ^ 2 = g)
    (hZ1 : ∀ z ∈ center G, z ^ 2 = 1 → z = 1 ∨ z = g) {L : Type} [Group L] [Finite L]
    (α : G →* L) (hα : Function.Surjective α) {c : L} (hc : PropBHypII L c) : c = α g := by
  obtain ⟨-, -, Q, -, -, ⟨p, n, _, hp2, -, ⟨e⟩⟩, hcZ, hcQ, hc2⟩ := hc
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have hnt : ∃ k, α k ≠ 1 := by
    obtain ⟨k, hk⟩ := hα c
    exact ⟨k, by rw [hk]; exact hc1⟩
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hG hnt
  rw [CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hG hα hker] at hcZ
  obtain ⟨z, hz, rfl⟩ := hcZ
  rcases hZ z hz with h1 | hzg
  · rcases hZ1 z hz h1 with rfl | rfl
    · exact absurd (map_one α) hc1
    · rfl
  · exfalso
    have hαg : α g = 1 := by rw [← hzg, map_pow, ← hc2, pow_orderOf_eq_one]
    have hkerg : ∀ x, α x = 1 → x = 1 ∨ x = g := by
      intro x hx
      have hxZ : x ∈ center G := hker hx
      rcases hZ x hxZ with hx1 | hxg
      · exact hZ1 x hxZ hx1
      · exfalso
        have hcomm : Commute z x⁻¹ := (mem_center_iff.1 hz x⁻¹).symm
        have hzx : (z * x⁻¹) ^ 2 = 1 := by
          rw [hcomm.mul_pow, hzg, inv_pow, hxg, mul_inv_cancel]
        rcases hZ1 (z * x⁻¹) (mul_mem hz (inv_mem hxZ)) hzx with h | h
        · have hzx' : z = x := mul_inv_eq_one.1 h
          exact hc1 (by rw [hzx', hx])
        · have hzx' : z = g * x := by rw [← h]; group
          exact hc1 (by rw [hzx', map_mul, hαg, hx, one_mul])
    have hF : ringChar (GaloisField p n) ≠ 2 := by
      rw [ringChar.eq (GaloisField p n) p]
      exact hp2
    exact false_of_central_sq hα hαg hkerg hg hg2 hz hzg hcQ hF e

theorem center_hyps_of_scalar {G : Type} [Group G] {F : Type} [Field F] (hF : ringChar F ≠ 2)
    (M : G →* Matrix (Fin 4) (Fin 4) F) (hM : Function.Injective M) {g : G} (hg : M g = -1)
    (hZ : ∀ z ∈ center G, ∃ r : F, r ^ 4 = 1 ∧ M z = r • 1) :
    orderOf g = 2 ∧ (∀ z ∈ center G, z ^ 2 = 1 ∨ z ^ 2 = g) ∧
      (∀ z ∈ center G, z ^ 2 = 1 → z = 1 ∨ z = g) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hne : (-1 : Matrix (Fin 4) (Fin 4) F) ≠ 1 := by
    intro h
    have := congrFun (congrFun h 0) 0
    simp only [Matrix.neg_apply, Matrix.one_apply_eq] at this
    exact h2 (by linear_combination -this)
  have hsq : ∀ z ∈ center G, ∀ r : F, M z = r • 1 → M (z ^ 2) = (r ^ 2) • 1 := by
    intro z _ r hr
    rw [map_pow, hr, smul_pow, one_pow]
  refine ⟨orderOf_eq_prime ?_ ?_, fun z hz => ?_, fun z hz hz1 => ?_⟩
  · apply hM
    rw [map_pow, hg, map_one, neg_one_sq]
  · intro h1
    apply hne
    rw [← hg, h1, map_one]
  · obtain ⟨r, hr4, hr⟩ := hZ z hz
    have hfac : (r ^ 2 - 1) * (r ^ 2 + 1) = 0 := by linear_combination hr4
    rcases mul_eq_zero.1 hfac with h | h
    · left
      apply hM
      rw [hsq z hz r hr, sub_eq_zero.1 h, one_smul, map_one]
    · right
      apply hM
      rw [hsq z hz r hr, eq_neg_of_add_eq_zero_left h, hg, neg_one_smul]
  · obtain ⟨r, -, hr⟩ := hZ z hz
    have h1 : (r ^ 2) • (1 : Matrix (Fin 4) (Fin 4) F) = 1 := by
      rw [← hsq z hz r hr, hz1, map_one]
    have hr2 : r ^ 2 = 1 := by
      have := congrFun (congrFun h1 0) 0
      simpa using this
    have hfac : (r - 1) * (r + 1) = 0 := by linear_combination hr2
    rcases mul_eq_zero.1 hfac with h | h
    · left
      apply hM
      rw [hr, sub_eq_zero.1 h, one_smul, map_one]
    · right
      apply hM
      rw [hr, eq_neg_of_add_eq_zero_left h, hg, neg_one_smul]

theorem burgoynePropBSL4CoverInput : BurgoynePropBSL4CoverInput := by
  intro F _ _ hF L _ _ α hα c hc g hg
  have hG : IsQuasisimple SL(4, F) := CatalogueBGeneralLinear.specialLinear_quasisimple 4 F
    (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
  set M : SL(4, F) →* Matrix (Fin 4) (Fin 4) F :=
    (Units.coeHom (Matrix (Fin 4) (Fin 4) F)).comp Matrix.SpecialLinearGroup.toGL with hMdef
  have hMx : ∀ x : SL(4, F), M x = (x : Matrix (Fin 4) (Fin 4) F) := fun x => rfl
  have hM : Function.Injective M := fun x y hxy => Subtype.ext (by rw [← hMx, ← hMx, hxy])
  have hgc : g ∈ center SL(4, F) := by
    refine Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨-1, by norm_num, ?_⟩
    rw [hg, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, neg_one_smul]
  obtain ⟨hg2, hZ, hZ1⟩ := center_hyps_of_scalar hF M hM (g := g) (by rw [hMx, hg])
    (fun z hz => by
      obtain ⟨r, hr, hre⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
      rw [Fintype.card_fin] at hr
      exact ⟨r, hr, by rw [hMx, ← hre, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩)
  exact eq_of_propBHypII hG hgc hg2 hZ hZ1 α hα hc

end CFSG.ComponentClassification.Burgoyne.B
