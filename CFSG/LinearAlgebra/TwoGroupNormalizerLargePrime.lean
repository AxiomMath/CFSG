module

public import CFSG.Walter.ReeOrder.JT.AuxWeights
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CFSG.RankThree.PartTwo.Sec13.Item135CritProof
import CFSG.LinearAlgebra.SteinbergBQAutomizerPermutation

public section

namespace CFSG.LinearAlgebra.TwoGroupNormalizer

open Module Subgroup CFSG.Walter.JT
open scoped commutatorElement TensorProduct
open CFSG.SectionRank.Ccomm (char_apply_mem characteristic_inf characteristic_centralizer)

theorem isPGroup_zpowers_of_pow_eq_one {G : Type*} [Group G] {r k : ℕ} {y : G}
    (hy : y ^ r ^ k = 1) : IsPGroup r (zpowers y) := by
  rintro ⟨g, m, rfl⟩
  refine ⟨k, Subtype.ext ?_⟩
  change (y ^ m) ^ r ^ k = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]

theorem natCast_card_ne_zero {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {G : Type*} [Group G]
    [Finite G] (hG : IsPGroup 2 G) : ((Nat.card G : ℕ) : K) ≠ 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hG.exists_card_eq
  rw [hn, Nat.cast_pow]
  exact pow_ne_zero n (by exact_mod_cast h2)

theorem mem_normalizer_map_of_characteristic {Γ : Type*} [Group Γ] {P : Subgroup Γ} {y : Γ}
    (hy : y ∈ normalizer (P : Set Γ)) {D : Subgroup P} (hD : D.Characteristic) :
    y ∈ normalizer ((D.map P.subtype : Subgroup Γ) : Set Γ) := by
  set α : MulAut P := P.normalizerMonoidHom ⟨y, hy⟩
  have hα : ∀ x : P, ((α x : P) : Γ) = y * x * y⁻¹ := fun _ => rfl
  rw [mem_normalizer_iff]
  intro n
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨α d, char_apply_mem hD α hd, hα d⟩
  · rintro ⟨d, hd, hdeq⟩
    have hnP : n ∈ P := (mem_normalizer_iff.mp hy n).mpr (by rw [← hdeq]; exact d.2)
    have h1 : α ⟨n, hnP⟩ = d := Subtype.ext (by rw [hα]; exact hdeq.symm)
    refine ⟨⟨n, hnP⟩, ?_, rfl⟩
    have h2 := char_apply_mem hD α⁻¹ hd
    rwa [← h1, MulAut.inv_apply_self] at h2

variable {K V Γ : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Group Γ] [Finite Γ]

theorem commute_of_mem_normalizer (h2 : (2 : K) ≠ 0) (hV : finrank K V ≤ 4)
    (ρ : Representation K Γ V) {P : Subgroup Γ} (hP : IsPGroup 2 P) (hinj : Set.InjOn ρ P)
    {r : ℕ} (hr : r.Prime) (hr16 : 16 < r) {y : Γ} (hy : y ∈ normalizer (P : Set Γ))
    {k : ℕ} (hyk : y ^ r ^ k = 1) : ∀ x ∈ P, y * x = x * y := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C₀, hC, -, hcrit⟩ := CFSG.RankThree.PartTwo.Sec13.CritProof.exists_isThompsonCritical hP
  obtain ⟨hchar, -, hcomm, -⟩ := hC
  haveI := hchar
  set α : MulAut P := P.normalizerMonoidHom ⟨y, hy⟩ with hαdef
  have hα : ∀ x : P, ((α x : P) : Γ) = y * x * y⁻¹ := fun _ => rfl
  set Z₀ : Subgroup P := C₀ ⊓ centralizer (C₀ : Set P) with hZ₀
  have hZ₀char : Z₀.Characteristic := by
    haveI := characteristic_centralizer C₀
    exact characteristic_inf _ _
  set C : Subgroup Γ := C₀.map P.subtype with hCdef
  set Z : Subgroup Γ := Z₀.map P.subtype with hZdef
  have hCP : C ≤ P := map_subtype_le _
  have hZP : Z ≤ P := map_subtype_le _
  have memC : ∀ x : P, (x : Γ) ∈ C ↔ x ∈ C₀ := fun x => mem_map_iff_mem P.subtype_injective
  have memZ : ∀ x : P, (x : Γ) ∈ Z ↔ x ∈ Z₀ := fun x => mem_map_iff_mem P.subtype_injective
  have hPpow : ∀ x ∈ P, ∃ m : ℕ, x ^ 2 ^ m = 1 := fun x hx => by
    obtain ⟨m, hm⟩ := hP ⟨x, hx⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hZC : ∀ n ∈ Z, ∀ c ∈ C, n * c = c * n := by
    rintro _ ⟨n, hn, rfl⟩ _ ⟨c, hc, rfl⟩
    have := mem_centralizer_iff.mp hn.2 c hc
    exact congrArg Subtype.val this.symm
  have hZle : Z ≤ C := map_mono inf_le_left
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, ρ a * ρ b = ρ b * ρ a := fun a ha b hb => by
    rw [← map_mul, ← map_mul, hZC a ha b (hZle hb)]
  have hZchar : ((Nat.card Z : ℕ) : K) ≠ 0 := natCast_card_ne_zero h2 (hP.to_le hZP)
  have hcommZ : ∀ a ∈ C, ∀ b ∈ C, a⁻¹ * b⁻¹ * a * b ∈ Z := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 : ⁅a⁻¹, b⁻¹⁆ ∈ Z₀ :=
      hcomm (commutator_mem_commutator (mem_top _) (C₀.inv_mem hb))
    have h2 := (memZ _).mpr h1
    simpa [commutatorElement_def] using h2
  have hyC := mem_normalizer_map_of_characteristic hy hchar
  have hyZ := mem_normalizer_map_of_characteristic hy hZ₀char
  have hyCm : ∀ c ∈ C, y * c * y⁻¹ ∈ C := fun c hc => (mem_normalizer_iff.mp hyC c).mp hc
  have hstep1 := map_conj_eq_of_isPGroup ρ Z hZcomm hZchar hr (by omega)
    (isPGroup_zpowers_of_pow_eq_one hyk) (zpowers_le.mpr hyZ)
  have hyZc : ∀ n ∈ Z, y * n = n * y := by
    intro n hn
    have h1 := hstep1 y (mem_zpowers y) n hn
    have h3 : y * n * y⁻¹ = n :=
      hinj (hZP ((mem_normalizer_iff.mp hyZ n).mp hn)) (hZP hn) h1
    calc y * n = y * n * y⁻¹ * y := by group
      _ = n * y := by rw [h3]
  set H : Subgroup Γ := centralizer (Z : Set Γ) with hHdef
  have hyH : y ∈ H := mem_centralizer_iff.mpr fun n hn => (hyZc n hn).symm
  have hCH : C ≤ H := fun c hc => mem_centralizer_iff.mpr fun n hn => hZC n hn c hc
  have hmaps : ∀ (χ : Z → K) (h : H), ∀ v ∈ weightSpace ρ Z χ, ρ h v ∈ weightSpace ρ Z χ := by
    intro χ h v hv
    rw [mem_weightSpace] at hv ⊢
    intro n
    have hnh : (n : Γ) * h = h * n := mem_centralizer_iff.mp h.2 n n.2
    rw [← Module.End.mul_apply, ← map_mul, hnh, map_mul, Module.End.mul_apply, hv n, map_smul]
  have hkey : ∀ (χ : Z → K), ∀ z ∈ C, ∀ c ∈ C, ∀ v ∈ weightSpace ρ Z χ,
      ρ ((y * z * y⁻¹) * c * (y * z * y⁻¹)⁻¹) v = ρ (z * c * z⁻¹) v := by
    intro χ z hz c hc v hv
    set W := weightSpace ρ Z χ with hW
    let σ : Representation K H W :=
      Representation.subrepresentation (ρ.comp H.subtype) W (fun g w hw => hmaps χ g w hw)
    have hσ : ∀ (g : H) (w : W), ((σ g w : W) : V) = ρ g w := fun _ _ => rfl
    let Ad : Representation K H (W →ₗ[K] W) := σ.linHom σ
    have hAd : ∀ (g : H) (T : W →ₗ[K] W) (w : W), Ad g T w = σ g (T (σ g⁻¹ w)) :=
      fun _ _ _ => rfl
    have hAdZ : ∀ (n : H), (n : Γ) ∈ Z → Ad n = 1 := by
      intro n hn
      have hs : ∀ (m : Γ) (hm : m ∈ Z) (u : V), u ∈ W → ρ m u = χ ⟨m, hm⟩ • u :=
        fun m hm u hu => (mem_weightSpace.mp hu) ⟨m, hm⟩
      have hn' : ((n : Γ))⁻¹ ∈ Z := Z.inv_mem hn
      have hinvσ : ∀ w : W, σ n⁻¹ w = χ ⟨_, hn'⟩ • w := fun w =>
        Subtype.ext (by rw [hσ]; exact hs _ hn' w w.2)
      have hσn : ∀ w : W, σ n w = χ ⟨_, hn⟩ • w := fun w =>
        Subtype.ext (by rw [hσ]; exact hs _ hn w w.2)
      have hab : ∀ w : W, (χ ⟨_, hn⟩ * χ ⟨_, hn'⟩) • w = w := by
        intro w
        have h1 : σ n (σ n⁻¹ w) = w := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        rw [hinvσ, map_smul, hσn, smul_smul, mul_comm] at h1
        exact h1
      refine LinearMap.ext fun T => LinearMap.ext fun w => ?_
      rw [hAd, hinvσ, map_smul, map_smul, hσn, smul_smul, mul_comm (χ _) (χ _), ← map_smul, hab]
      rfl
    have hAdcomm : ∀ a ∈ C.subgroupOf H, ∀ b ∈ C.subgroupOf H, Ad a * Ad b = Ad b * Ad a := by
      intro a ha b hb
      have hn := hcommZ a (mem_subgroupOf.mp ha) b (mem_subgroupOf.mp hb)
      have hnH : (a : Γ)⁻¹ * (b : Γ)⁻¹ * a * b ∈ H := H.mul_mem (H.mul_mem (H.mul_mem
        (H.inv_mem a.2) (H.inv_mem b.2)) a.2) b.2
      have he : a * b = b * a * ⟨(a : Γ)⁻¹ * (b : Γ)⁻¹ * a * b, hnH⟩ := Subtype.ext (by
        show (a : Γ) * b = b * a * ((a : Γ)⁻¹ * (b : Γ)⁻¹ * a * b)
        group)
      rw [← map_mul, ← map_mul, he, map_mul, hAdZ ⟨_, hnH⟩ hn, mul_one]
    have hCchar : ((Nat.card (C.subgroupOf H) : ℕ) : K) ≠ 0 := by
      refine natCast_card_ne_zero h2 fun g => ?_
      obtain ⟨m, hm⟩ := hPpow (g : H) (hCP (mem_subgroupOf.mp g.2))
      exact ⟨m, Subtype.ext (Subtype.ext (by simpa using hm))⟩
    have hfin : finrank K (W →ₗ[K] W) < r := by
      rw [Module.finrank_linearMap]
      have hW4 : finrank K W ≤ 4 := (Submodule.finrank_le W).trans hV
      nlinarith
    set y' : H := ⟨y, hyH⟩
    have hy'k : y' ^ r ^ k = 1 := Subtype.ext (by simpa using hyk)
    have hRN : zpowers y' ≤ normalizer ((C.subgroupOf H : Subgroup H) : Set H) := by
      rw [zpowers_le, mem_normalizer_iff]
      intro g
      rw [mem_subgroupOf, mem_subgroupOf]
      exact mem_normalizer_iff.mp hyC g
    have hconj := map_conj_eq_of_isPGroup Ad (C.subgroupOf H) hAdcomm hCchar hr hfin
      (isPGroup_zpowers_of_pow_eq_one hy'k) hRN y' (mem_zpowers y') ⟨z, hCH hz⟩
      (mem_subgroupOf.mpr hz)
    have hT := LinearMap.congr_fun (LinearMap.congr_fun hconj (σ ⟨c, hCH hc⟩)) ⟨v, hv⟩
    have hT' := congrArg Subtype.val hT
    simp only [hAd, hσ] at hT'
    simpa [y', map_mul, Module.End.mul_apply, mul_assoc] using hT'
  have htop := (iSupIndep_weightSpace_and_iSup_eq_top ρ Z hZcomm hZchar).2
  have hCfix : ∀ z ∈ C, y * z * y⁻¹ = z := by
    intro z hz
    have haC : y * z * y⁻¹ ∈ C := hyCm z hz
    set w := z⁻¹ * (y * z * y⁻¹) with hwdef
    have hwC : w ∈ C := C.mul_mem (C.inv_mem hz) haC
    have hwc : ∀ c ∈ C, w * c = c * w := by
      intro c hc
      have hle : ∀ χ, weightSpace ρ Z χ ≤ LinearMap.eqLocus
          (ρ ((y * z * y⁻¹) * c * (y * z * y⁻¹)⁻¹)) (ρ (z * c * z⁻¹)) :=
        fun χ v hv => hkey χ z hz c hc v hv
      have h1 : LinearMap.eqLocus (ρ ((y * z * y⁻¹) * c * (y * z * y⁻¹)⁻¹))
          (ρ (z * c * z⁻¹)) = ⊤ := by
        rw [eq_top_iff, ← htop]
        exact iSup_le hle
      have h2 := LinearMap.eqLocus_eq_top.mp h1
      have h3 : (y * z * y⁻¹) * c * (y * z * y⁻¹)⁻¹ = z * c * z⁻¹ :=
        hinj (hCP (C.mul_mem (C.mul_mem haC hc) (C.inv_mem haC)))
          (hCP (C.mul_mem (C.mul_mem hz hc) (C.inv_mem hz))) h2
      calc w * c = z⁻¹ * ((y * z * y⁻¹) * c * (y * z * y⁻¹)⁻¹) * (y * z * y⁻¹) := by
            rw [hwdef]; group
        _ = z⁻¹ * (z * c * z⁻¹) * (y * z * y⁻¹) := by rw [h3]
        _ = c * w := by rw [hwdef]; group
    have hwZ : w ∈ Z := by
      have hwP : w ∈ P := hCP hwC
      rw [show w = ((⟨w, hwP⟩ : P) : Γ) from rfl, memZ]
      refine ⟨(memC _).mp hwC, mem_centralizer_iff.mpr fun c hc => Subtype.ext ?_⟩
      exact (hwc c ((memC c).mpr hc)).symm
    have hyw : Commute y w := hyZc w hwZ
    have hiter : ∀ j : ℕ, y ^ j * z * (y ^ j)⁻¹ = z * w ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hyz : y * z * y⁻¹ = z * w := by rw [hwdef]; group
        calc y ^ (j + 1) * z * (y ^ (j + 1))⁻¹ = y * (y ^ j * z * (y ^ j)⁻¹) * y⁻¹ := by
              rw [pow_succ']; group
          _ = y * z * y⁻¹ * (y * w ^ j * y⁻¹) := by rw [ih]; group
          _ = z * w * w ^ j := by
              rw [hyz, (hyw.pow_right j).eq, mul_inv_cancel_right]
          _ = z * w ^ (j + 1) := by rw [pow_succ', mul_assoc]
    have hwr : w ^ r ^ k = 1 := by
      have := hiter (r ^ k)
      rw [hyk, one_mul, inv_one, mul_one] at this
      exact (mul_eq_left.mp this.symm)
    obtain ⟨m, hm⟩ := hPpow w (hCP hwC)
    have hcop : Nat.Coprime (r ^ k) (2 ^ m) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hr Nat.prime_two).mpr (by omega))
    have hw1 : w = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hwr) (orderOf_dvd_of_pow_eq_one hm))
    calc y * z * y⁻¹ = z * w := by rw [hwdef]; group
      _ = z := by rw [hw1, mul_one]
  have hαr : α ^ r ^ k = 1 := by
    rw [hαdef, ← map_pow]
    have : (⟨y, hy⟩ : normalizer (P : Set Γ)) ^ r ^ k = 1 := Subtype.ext (by simpa using hyk)
    rw [this, map_one]
  have hαcop : Nat.Coprime (orderOf α) 2 :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hαr)
      (Nat.Coprime.pow_left _ ((Nat.coprime_primes hr Nat.prime_two).mpr (by omega)))
  have hα1 : α = 1 := hcrit α hαcop fun x hx => Subtype.ext (by
    rw [hα]; exact hCfix x ((memC x).mpr hx))
  intro x hx
  have h1 := congrArg Subtype.val (DFunLike.congr_fun hα1 ⟨x, hx⟩)
  rw [hα] at h1
  change y * x * y⁻¹ = x at h1
  calc y * x = y * x * y⁻¹ * y := by group
    _ = x * y := by rw [h1]

theorem false_of_surjective {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (h2 : (2 : K) ≠ 0) (hW : finrank K W ≤ 4)
    {Γ S : Type*} [Group Γ] [Finite Γ] [Group S]
    (ρ : Γ →* LinearMap.GeneralLinearGroup K W)
    (hker : ∀ x : Γ, ρ x = 1 → ∀ m : ℕ, x ^ 2 ^ m = 1 → x = 1)
    (φ : Γ →* S) (hφ : Function.Surjective φ) (Q : Subgroup S) (hQ : IsPGroup 2 Q)
    (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) {h : S} (hh : h ∈ normalizer (Q : Set S))
    {r : ℕ} (hr : r.Prime) (hr16 : 16 < r) (hhr : h ^ r = 1)
    {u : S} (hu : u ∈ Q) (hne : h * u ≠ u * h) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := AlgebraicClosure K
  let R : Representation L Γ (L ⊗[K] W) :=
    (Module.End.baseChangeHom K L W).toMonoidHom.comp ((Units.coeHom _).comp ρ)
  have hR : ∀ x, R x = SteinbergBQ.bcEnd L (ρ x) := fun _ => rfl
  have h2L : (2 : L) ≠ 0 := by
    intro h0
    apply h2
    have : algebraMap K L 2 = 0 := by rw [map_ofNat]; exact h0
    exact (map_eq_zero_iff (algebraMap K L) (algebraMap K L).injective).mp this
  have hfin : finrank L (L ⊗[K] W) ≤ 4 := by rw [Module.finrank_baseChange]; exact hW
  set Y : Subgroup Γ := Q.comap φ with hYdef
  set G₀ : Subgroup Γ := normalizer (Y : Set Γ) with hG₀def
  obtain ⟨g, hg⟩ := hφ h
  have hgG₀ : g ∈ G₀ := by
    rw [hG₀def, mem_normalizer_iff]
    intro x
    change φ x ∈ Q ↔ φ (g * x * g⁻¹) ∈ Q
    rw [map_mul, map_mul, map_inv, hg]
    exact mem_normalizer_iff.mp hh (φ x)
  set N : Subgroup G₀ := Y.subgroupOf G₀ with hNdef
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 2 N))
  have hF := Sylow.normalizer_sup_eq_top P
  have hgmem : (⟨g, hgG₀⟩ : G₀) ∈ ((normalizer ((P.map N.subtype : Subgroup G₀) : Set G₀) ⊔ N :
      Subgroup G₀) : Set G₀) := by rw [hF]; exact mem_top _
  rw [mul_normal] at hgmem
  obtain ⟨a, ha, b, hb, hab⟩ := hgmem
  set P₀ : Subgroup G₀ := P.map N.subtype with hP₀def
  have hP₀ : IsPGroup 2 P₀ := P.isPGroup'.map _
  have hvQ : φ (b : Γ) ∈ Q := mem_subgroupOf.mp hb
  have hφa : φ (a : Γ) = h * (φ (b : Γ))⁻¹ := by
    rw [← hg, ← map_inv, ← map_mul]
    congr 1
    have := congrArg Subtype.val hab
    simp only [Subgroup.coe_mul] at this
    rw [← this, mul_inv_cancel_right]
  let R₀ : Representation L G₀ (L ⊗[K] W) := R.comp G₀.subtype
  have hinj : Set.InjOn R₀ P₀ := by
    intro x hx z hz hxz
    have h1 : R₀ (x⁻¹ * z) = 1 := by rw [map_mul, ← hxz, ← map_mul, inv_mul_cancel, map_one]
    have h2' : ρ ((x⁻¹ * z : G₀) : Γ) = 1 := by
      apply SteinbergBQ.bcEnd_injective L
      rw [← hR, SteinbergBQ.bcEnd_one]
      exact h1
    obtain ⟨m, hm⟩ := hP₀ ⟨x⁻¹ * z, P₀.mul_mem (P₀.inv_mem hx) hz⟩
    have hm' : ((x⁻¹ * z : G₀) : Γ) ^ 2 ^ m = 1 := by
      simpa using congrArg (fun t : P₀ => ((t : G₀) : Γ)) hm
    have h3 := hker _ h2' m hm'
    have h4 : x⁻¹ * z = 1 := Subtype.ext h3
    rw [inv_mul_eq_one] at h4
    exact h4
  obtain ⟨e, m, hrm, hom⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos a).ne' r hr.one_lt.ne'
  have hy : a ^ m ∈ normalizer (P₀ : Set G₀) := pow_mem ha m
  have hye : (a ^ m) ^ r ^ e = 1 := by
    rw [← pow_mul, mul_comm, ← hom, pow_orderOf_eq_one]
  have hcomm := commute_of_mem_normalizer h2L hfin R₀ hP₀ hinj hr hr16 hy hye
  let f : N →* Q := (φ.comp (G₀.subtype.comp N.subtype)).codRestrict Q fun x => x.2
  have hf : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨t, ht⟩ := hφ q
    have htY : t ∈ Y := by change φ t ∈ Q; rw [ht]; exact hq
    exact ⟨⟨⟨t, le_normalizer htY⟩, htY⟩, Subtype.ext ht⟩
  have htop : ((P.mapSurjective hf : Sylow 2 Q) : Subgroup Q) = ⊤ :=
    ((P.mapSurjective hf).is_maximal' (IsPGroup.of_equiv hQ Subgroup.topEquiv.symm)
      le_top).symm
  have huimg : (⟨u, hu⟩ : Q) ∈ ((P.mapSurjective hf : Sylow 2 Q) : Subgroup Q) := by
    rw [htop]; exact mem_top _
  rw [Sylow.coe_mapSurjective] at huimg
  obtain ⟨x, hxP, hxu⟩ := huimg
  have hxu' : φ (((x : N) : G₀) : Γ) = u := congrArg Subtype.val hxu
  have hc := hcomm (N.subtype x) ⟨x, hxP, rfl⟩
  have hc' := congrArg (fun t : G₀ => φ (t : Γ)) hc
  simp only [Subgroup.coe_mul, SubgroupClass.coe_pow, map_mul, map_pow, hφa, Subgroup.coe_subtype,
    hxu'] at hc'
  have hpowQ : ∀ j : ℕ, ∃ v' ∈ Q, (h * (φ (b : Γ))⁻¹) ^ j = h ^ j * v' := by
    intro j
    induction j with
    | zero => exact ⟨1, Q.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨v', hv', hj⟩ := ih
      have hhinv : h⁻¹ ∈ normalizer (Q : Set S) := inv_mem hh
      have h1 : h⁻¹ * v' * h ∈ Q := by
        have := (mem_normalizer_iff.mp hhinv v').mp hv'
        rwa [inv_inv] at this
      refine ⟨h⁻¹ * v' * h * (φ (b : Γ))⁻¹, Q.mul_mem h1 (Q.inv_mem hvQ), ?_⟩
      rw [pow_succ, hj, pow_succ]
      group
  obtain ⟨v', hv', hvm⟩ := hpowQ m
  rw [hvm] at hc'
  have hhm : h ^ m * u = u * h ^ m := by
    have h1 : h ^ m * v' * u = u * (h ^ m * v') := hc'
    have h3 : v' * u = u * v' := hQab v' hv' u hu
    have h4 : h ^ m * u * v' = u * h ^ m * v' := by
      calc h ^ m * u * v' = h ^ m * (u * v') := by group
        _ = h ^ m * (v' * u) := by rw [h3]
        _ = h ^ m * v' * u := by group
        _ = u * (h ^ m * v') := h1
        _ = u * h ^ m * v' := by group
    exact mul_right_cancel h4
  have hcop : m.Coprime (orderOf h) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hhr)
      ((Nat.Prime.coprime_iff_not_dvd hr).mpr hrm).symm
  obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
  apply hne
  have : Commute (h ^ m) u := hhm
  rw [← hc]
  exact (this.pow_left c).eq

end CFSG.LinearAlgebra.TwoGroupNormalizer
