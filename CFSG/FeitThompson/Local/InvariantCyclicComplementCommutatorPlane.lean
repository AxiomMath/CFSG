module

public import CFSG.FeitThompson.Local.AutomorphismsFixingPlaneQuotientAbelian
public import CFSG.FeitThompson.Local.QuadraticActionsDescendSections
public import CFSG.FeitThompson.Local.ClassTwoPrimeTorsionCharacteristic
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.NoncentralTorsionCubeCommutatorPlane
import CFSG.FeitThompson.Local.InvariantCyclicComplementPrimeLine
import CFSG.FeitThompson.Local.PrimeCubeTorsionCentralizerCyclic

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup
open scoped commutatorElement Pointwise

variable {p : ℕ} {R : Type*} [Group R] {A : Type*} [Group A]

theorem apply_mem_of_characteristic (ρ : A →* MulAut R) (N : Subgroup R) [N.Characteristic]
    (a : A) {x : R} (hx : x ∈ N) : ρ a x ∈ N :=
  (Subgroup.characteristic_iff_map_eq.1 ‹N.Characteristic› (ρ a)) ▸
    (⟨x, hx, rfl⟩ : ρ a x ∈ N.map ((ρ a : R ≃* R) : R →* R))

theorem mem_map_subtype_iff {D : Subgroup R} {X : Subgroup ↥D} {x : R} (hx : x ∈ D) :
    x ∈ X.map D.subtype ↔ (⟨x, hx⟩ : ↥D) ∈ X := by
  refine ⟨?_, fun h => ⟨⟨x, hx⟩, h, rfl⟩⟩
  rintro ⟨y, hy, hyx⟩
  have hy2 : y = (⟨x, hx⟩ : ↥D) := Subtype.ext hyx
  exact hy2 ▸ hy

private theorem isInvariantSubgroup_of_forall {ρ : A →* MulAut R} {N : Subgroup R}
    (h : ∀ a : A, ∀ x ∈ N, ρ a x ∈ N) : IsInvariantSubgroup ρ N :=
  isInvariantSubgroup_iff_forall_map_eq.2 (map_eq_of_invariant ρ h)

theorem isInvariantSubgroup_subgroupOf_restrictAut {ρ : A →* MulAut R} {D : Subgroup R}
    (hD : IsInvariantSubgroup ρ D) {N : Subgroup R} (hN : ∀ a : A, ∀ x ∈ N, ρ a x ∈ N) :
    IsInvariantSubgroup hD.restrictAut (N.subgroupOf D) := by
  refine isInvariantSubgroup_of_forall fun a x hx => ?_
  rw [mem_subgroupOf] at hx ⊢
  rw [hD.coe_restrictAut_apply]
  exact hN a _ hx

theorem forall_mul_comm_quotient_subgroupOf {C D : Subgroup R} [C.Normal]
    (h : ∀ d ∈ D, ∀ e ∈ D, ⁅d, e⁆ ∈ C) : ∀ x y : ↥D ⧸ C.subgroupOf D, x * y = y * x := by
  have h2 : _root_.commutator ↥D ≤ C.subgroupOf D := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro g1 _ g2 _
    rw [mem_subgroupOf]
    have h3 : ((⁅g1, g2⁆ : ↥D) : R) = ⁅(g1 : R), (g2 : R)⁆ := by
      rw [commutatorElement_def, commutatorElement_def]; push_cast; rfl
    rw [h3]
    exact h _ g1.2 _ g2.2
  have h4 := (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := C.subgroupOf D)).2 h2
  exact fun x y => h4.is_comm.comm x y

theorem pow_eq_one_quotient_subgroupOf {C D : Subgroup R} [C.Normal]
    (h : ∀ d ∈ D, d ^ p ∈ C) : ∀ x : ↥D ⧸ C.subgroupOf D, x ^ p = 1 := by
  intro x
  induction x using QuotientGroup.induction_on with
  | _ y =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    have h3 : ((y ^ p : ↥D) : R) = (y : R) ^ p := by push_cast; rfl
    rw [h3]
    exact h _ y.2

theorem isMulCommutative_autFixingQuotient {B : Type*} [Group B] {T : Subgroup B} (hp : p.Prime)
    (hB : Nat.card B = p ^ 3) (hexp : ∀ b : B, b ^ p = 1) (hT : Nat.card T = p ^ 2) :
    IsMulCommutative ↥(autFixingQuotient T) := by
  obtain ⟨d, -, -, ⟨f⟩⟩ := autFixingQuotient_elementaryAbelian hp hB hexp hT
  exact ⟨⟨fun a b => f.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩

theorem pow_eq_one_of_mem_autFixingQuotient {B : Type*} [Group B] {T : Subgroup B} (hp : p.Prime)
    (hB : Nat.card B = p ^ 3) (hexp : ∀ b : B, b ^ p = 1) (hT : Nat.card T = p ^ 2)
    (a : ↥(autFixingQuotient T)) : a ^ p = 1 := by
  obtain ⟨d, -, -, ⟨f⟩⟩ := autFixingQuotient_elementaryAbelian hp hB hexp hT
  exact f.injective (by rw [map_pow, map_one, pow_eq_one_pi_multiplicative_zmod])

def conjAutOfSubgroup (B : Subgroup R) [B.Normal] (D : Subgroup R) : ↥D →* MulAut ↥B :=
  MulAut.conjNormal.comp D.subtype

@[simp]
theorem coe_conjAutOfSubgroup_apply_apply (B : Subgroup R) [B.Normal] (D : Subgroup R) (d : ↥D)
    (b : ↥B) : ((conjAutOfSubgroup B D d b : ↥B) : R) = (d : R) * (b : R) * (d : R)⁻¹ :=
  MulAut.conjNormal_apply _ _

theorem ker_conjAutOfSubgroup (B : Subgroup R) [B.Normal] (D : Subgroup R) :
    (conjAutOfSubgroup B D).ker = (centralizer (B : Set R)).subgroupOf D := by
  ext d
  rw [MonoidHom.mem_ker, mem_subgroupOf, mem_centralizer_iff]
  constructor
  · intro h b hb
    have h2 := congrArg (fun x : ↥B => (x : R)) (DFunLike.congr_fun h (⟨b, hb⟩ : ↥B))
    simp only [coe_conjAutOfSubgroup_apply_apply, MulAut.one_apply] at h2
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  · intro h
    ext b
    rw [coe_conjAutOfSubgroup_apply_apply, MulAut.one_apply, ← h (b : R) b.2]
    group

theorem conjAutOfSubgroup_mem_autFixingQuotient {B T D : Subgroup R} [B.Normal]
    (hcomm : ⁅(⊤ : Subgroup R), B⁆ ≤ T) (hD : D ≤ centralizer (T : Set R)) (d : ↥D) :
    conjAutOfSubgroup B D d ∈ autFixingQuotient (T.subgroupOf B) := by
  rw [mem_autFixingQuotient]
  refine ⟨fun t ht => ?_, fun b => ?_⟩
  · rw [mem_subgroupOf] at ht
    refine Subtype.ext ?_
    rw [coe_conjAutOfSubgroup_apply_apply]
    have h := (mem_centralizer_iff.mp (hD d.2)) (t : R) ht
    rw [← h, mul_assoc, mul_inv_cancel, mul_one]
  · rw [eq_comm, QuotientGroup.eq, mem_subgroupOf]
    have h : ((b⁻¹ * conjAutOfSubgroup B D d b : ↥B) : R) = ⁅(b : R)⁻¹, (d : R)⁆ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjAutOfSubgroup_apply_apply,
        commutatorElement_def]
      group
    rw [h]
    exact hcomm ((Subgroup.commutator_comm B ⊤).le
      (Subgroup.commutator_mem_commutator (inv_mem b.2) (mem_top _)))

theorem commutatorElement_mem_and_pow_mem_centralizer {B T D : Subgroup R} [B.Normal]
    (hp : p.Prime) (hB : Nat.card ↥B = p ^ 3) (hexp : ∀ b : ↥B, b ^ p = 1)
    (hT : Nat.card ↥(T.subgroupOf B) = p ^ 2)
    (hcomm : ⁅(⊤ : Subgroup R), B⁆ ≤ T) (hD : D ≤ centralizer (T : Set R)) :
    (∀ d ∈ D, ∀ e ∈ D, ⁅d, e⁆ ∈ centralizer (B : Set R)) ∧
      ∀ d ∈ D, d ^ p ∈ centralizer (B : Set R) := by
  set K := autFixingQuotient (T.subgroupOf B) with hK
  set ψ : ↥D →* ↥K :=
    (conjAutOfSubgroup B D).codRestrict K (conjAutOfSubgroup_mem_autFixingQuotient hcomm hD)
    with hψ
  have hker : ψ.ker = (centralizer (B : Set R)).subgroupOf D := by
    rw [hψ, MonoidHom.ker_codRestrict, ker_conjAutOfSubgroup]
  have hKcomm : IsMulCommutative ↥K := isMulCommutative_autFixingQuotient hp hB hexp hT
  have hKexp : ∀ a : ↥K, a ^ p = 1 := pow_eq_one_of_mem_autFixingQuotient hp hB hexp hT
  refine ⟨fun d hd e he => ?_, fun d hd => ?_⟩
  · have h1 : ψ ⁅(⟨d, hd⟩ : ↥D), (⟨e, he⟩ : ↥D)⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hKcomm.is_comm.comm _ _
    have h2 : ⁅(⟨d, hd⟩ : ↥D), (⟨e, he⟩ : ↥D)⁆ ∈ ψ.ker := MonoidHom.mem_ker.2 h1
    rw [hker, mem_subgroupOf] at h2
    have h3 : ((⁅(⟨d, hd⟩ : ↥D), (⟨e, he⟩ : ↥D)⁆ : ↥D) : R) = ⁅d, e⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      push_cast
      rfl
    rwa [h3] at h2
  · have h1 : ψ ((⟨d, hd⟩ : ↥D) ^ p) = 1 := by rw [map_pow, hKexp]
    have h2 : (⟨d, hd⟩ : ↥D) ^ p ∈ ψ.ker := MonoidHom.mem_ker.2 h1
    rw [hker, mem_subgroupOf] at h2
    have h3 : (((⟨d, hd⟩ : ↥D) ^ p : ↥D) : R) = d ^ p := by push_cast; rfl
    rwa [h3] at h2

theorem exists_invariant_sup_eq_inf_eq [Finite A] (ρ : A →* MulAut R) {C T D : Subgroup R}
    [C.Normal] (hCD : C ≤ D) (hTD : T ≤ D) (hCinv : ∀ a : A, ∀ x ∈ C, ρ a x ∈ C)
    (hTinv : ∀ a : A, ∀ x ∈ T, ρ a x ∈ T) (hDinv : ∀ a : A, ∀ x ∈ D, ρ a x ∈ D) (hp : p.Prime)
    (hA : ¬ p ∣ Nat.card A) (hab : ∀ x y : ↥D ⧸ C.subgroupOf D, x * y = y * x)
    (hexp : ∀ x : ↥D ⧸ C.subgroupOf D, x ^ p = 1) :
    ∃ X : Subgroup R, (∀ a : A, ∀ x ∈ X, ρ a x ∈ X) ∧ C ≤ X ∧ X ≤ D ∧ T ⊔ X = D ∧
      T ⊓ X = T ⊓ C := by
  have hDI : IsInvariantSubgroup ρ D := isInvariantSubgroup_of_forall hDinv
  set σ : A →* MulAut ↥D := hDI.restrictAut with hσ
  have hσcoe : ∀ (a : A) (x : ↥D), ((σ a x : ↥D) : R) = ρ a (x : R) := fun a x =>
    hDI.coe_restrictAut_apply a x
  have hCsub : IsInvariantSubgroup σ (C.subgroupOf D) :=
    isInvariantSubgroup_subgroupOf_restrictAut hDI hCinv
  have hTsub : IsInvariantSubgroup σ (T.subgroupOf D) :=
    isInvariantSubgroup_subgroupOf_restrictAut hDI hTinv
  set β : A →* MulAut (↥D ⧸ C.subgroupOf D) := hCsub.quotientAut with hβ
  set π : ↥D →* ↥D ⧸ C.subgroupOf D := QuotientGroup.mk' (C.subgroupOf D) with hπ
  have hπker : π.ker = C.subgroupOf D := QuotientGroup.ker_mk' _
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hequiv : ∀ (a : A) (x : ↥D), π (σ a x) = β a (π x) := by
    intro a x
    rw [hβ, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hCsub.quotientAut_mk]
  let _ : CommGroup (↥D ⧸ C.subgroupOf D) :=
    { (inferInstance : Group (↥D ⧸ C.subgroupOf D)) with mul_comm := hab }
  set S : Subgroup (↥D ⧸ C.subgroupOf D) := (T.subgroupOf D).map π with hS
  have hSinv : ∀ a : A, ∀ x ∈ S, β a x ∈ S := by
    rintro a x ⟨y, hy, rfl⟩
    exact ⟨σ a y, hTsub.apply_mem a hy, hequiv a y⟩
  obtain ⟨U, hUinv, hcompl⟩ := exists_invariant_isCompl_of_pow_eq_one hp hexp β hA hSinv
  set X' : Subgroup ↥D := U.comap π with hX'
  have hkerX' : C.subgroupOf D ≤ X' := hπker ▸ π.ker_le_comap U
  have hCX : C ≤ X'.map D.subtype := fun c hc =>
    (mem_map_subtype_iff (hCD hc)).2 (hkerX' (mem_subgroupOf.2 hc))
  refine ⟨X'.map D.subtype, ?_, hCX, Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro a y hy
    have hyD : y ∈ D := Subgroup.map_subtype_le _ hy
    rw [mem_map_subtype_iff hyD] at hy
    have hρyD : ρ a y ∈ D := hDinv a y hyD
    rw [mem_map_subtype_iff hρyD]
    have he : (⟨ρ a y, hρyD⟩ : ↥D) = σ a ⟨y, hyD⟩ := Subtype.ext (hσcoe a ⟨y, hyD⟩).symm
    rw [he, hX', Subgroup.mem_comap, hequiv]
    exact hUinv a _ (Subgroup.mem_comap.1 hy)
  · have key : T.subgroupOf D ⊔ X' = ⊤ := by
      have h1 : (T.subgroupOf D ⊔ X').map π = ⊤ := by
        rw [Subgroup.map_sup, hX', Subgroup.map_comap_eq_self_of_surjective hπsurj, ← hS,
          hcompl.sup_eq_top]
      have h2 := congrArg (fun N => N.comap π) h1
      rwa [Subgroup.comap_map_eq, hπker, sup_of_le_left (le_sup_of_le_right hkerX'),
        Subgroup.comap_top] at h2
    have h3 := congrArg (fun N => N.map D.subtype) key
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hTD, ← MonoidHom.range_eq_map,
      Subgroup.subtype_range] at h3
  · refine le_antisymm (fun x hx => ?_) (inf_le_inf_left T hCX)
    obtain ⟨hxT, hxX⟩ := Subgroup.mem_inf.1 hx
    have hxD : x ∈ D := hTD hxT
    rw [mem_map_subtype_iff hxD] at hxX
    have hmem : π (⟨x, hxD⟩ : ↥D) ∈ S ⊓ U :=
      ⟨⟨⟨x, hxD⟩, mem_subgroupOf.2 hxT, rfl⟩, Subgroup.mem_comap.1 hxX⟩
    rw [hcompl.inf_eq_bot, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_inf.2 ⟨hxT, mem_subgroupOf.1 (hπker ▸ (MonoidHom.mem_ker.2 hmem))⟩

theorem isCyclic_of_pow_eq_one_mem [Finite R] (hp : p.Prime) (hodd : Odd p) (hR : IsPGroup p R)
    {X Z : Subgroup R} (hZ : Nat.card Z = p) (htors : ∀ x ∈ X, x ^ p = 1 → x ∈ Z) :
    IsCyclic ↥X := by
  by_contra hnc
  have hncTop : ¬ IsCyclic (⊤ : Subgroup ↥X) := fun _ =>
    hnc (isCyclic_of_surjective (⊤ : Subgroup ↥X).subtype fun x => ⟨⟨x, trivial⟩, rfl⟩)
  obtain ⟨E, -, -, ⟨f⟩⟩ := exists_normal_le_mulEquiv_pi_of_not_isCyclic hp hodd
    (hR.to_subgroup X) (⊤ : Subgroup ↥X) hncTop
  have hle : E.map X.subtype ≤ Z := by
    rintro y ⟨x, hx, rfl⟩
    refine htors _ x.2 ?_
    have h1 : (⟨x, hx⟩ : ↥E) ^ p = 1 := by
      apply f.injective
      rw [map_pow, map_one, pow_eq_one_pi_multiplicative_zmod]
    exact congrArg (Subgroup.subtype X) (congrArg (Subgroup.subtype E) h1)
  have hdvd : p ^ 2 ∣ p := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [← Nat.card_congr (equivMapOfInjective E X.subtype X.subtype_injective).toEquiv,
      Nat.card_congr f.toEquiv, card_pi_multiplicative_zmod, hZ] at h
  have hle2 : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hdvd
  have h2 := hp.two_le
  nlinarith

theorem exists_invariant_isCyclic_complement_commutator_plane [Finite R] [Finite A] (hp : p.Prime)
    (hodd : Odd p) (hR : IsPGroup p R) (hB : Nat.card ↥(omega1 p R) = p ^ 3)
    (hnab : ¬ IsMulCommutative ↥(omega1 p R)) (hexp : ∀ b ∈ omega1 p R, b ^ p = 1)
    (hZ : ¬ ⁅(⊤ : Subgroup R), omega1 p R⁆
      ≤ (center ↥(omega1 p R)).map (omega1 p R).subtype)
    (ρ : A →* MulAut R) (hA : ¬ p ∣ Nat.card A) :
    ∃ X : Subgroup R, IsInvariantSubgroup ρ X ∧ IsCyclic ↥X ∧
      X ≤ centralizer ((⁅(⊤ : Subgroup R), omega1 p R⁆ : Subgroup R) : Set R) ∧
      centralizer (omega1 p R : Set R) ≤ X ∧
      ⁅(⊤ : Subgroup R), omega1 p R⁆ ⊔ X
        = centralizer ((⁅(⊤ : Subgroup R), omega1 p R⁆ : Subgroup R) : Set R) ∧
      ⁅(⊤ : Subgroup R), omega1 p R⁆ ⊓ X
        = (center ↥(omega1 p R)).map (omega1 p R).subtype ∧
      omega1 p R ⊔ X = ⊤ ∧
      omega1 p R ⊓ X = (center ↥(omega1 p R)).map (omega1 p R).subtype := by
  have : Fact p.Prime := ⟨hp⟩
  set B : Subgroup R := omega1 p R with hBdef
  set Z : Subgroup R := (center ↥(omega1 p R)).map (omega1 p R).subtype with hZdef
  set T : Subgroup R := ⁅(⊤ : Subgroup R), B⁆ with hTdef
  set C : Subgroup R := centralizer (B : Set R) with hCdef
  set D : Subgroup R := centralizer (T : Set R) with hDdef
  have hTcard : Nat.card ↥T = p ^ 2 := card_commutator_top_omega1 hp hR hB hnab hZ
  have hTB : T ≤ B := Subgroup.commutator_le_right _ _
  have hTD : T ≤ D := by
    have : IsMulCommutative ↥T := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hTcard
    exact Subgroup.le_centralizer _
  have hCD : C ≤ D := centralizer_omega1_le_centralizer_commutator p R
  have hZT : Z ≤ T := map_center_le_commutator_top_omega1 hp hB hnab
  have hZcard : Nat.card ↥Z = p := card_map_center_omega1 hp hB hnab
  have hBinfD : B ⊓ D = T := inf_centralizer_commutator_top_omega1 hp hR hB hnab hZ
  have hBinfC : B ⊓ C = Z := inf_centralizer_omega1_eq_map_center p R
  have hBDtop : B ⊔ D = ⊤ := sup_centralizer_commutator_top_omega1 hp hR hB hnab hZ
  have hTCZ : T ⊓ C = Z := by
    rw [← inf_eq_left.mpr hTB, inf_assoc, hBinfC, inf_eq_right.mpr hZT]
  have hTsubcard : Nat.card ↥(T.subgroupOf B) = p ^ 2 := by rw [card_subgroupOf hTB, hTcard]
  have hexpB : ∀ b : ↥B, b ^ p = 1 := fun b => Subtype.ext (by push_cast; exact hexp _ b.2)
  obtain ⟨hDcomm, hDpow⟩ := commutatorElement_mem_and_pow_mem_centralizer (B := B) (T := T)
    (D := D) hp hB hexpB hTsubcard le_rfl le_rfl
  obtain ⟨X, hXinv, hCX, hXD, hTX, hTinfX⟩ := exists_invariant_sup_eq_inf_eq ρ hCD hTD
    (fun a x hx => apply_mem_of_characteristic ρ C a hx)
    (fun a x hx => apply_mem_of_characteristic ρ T a hx)
    (fun a x hx => apply_mem_of_characteristic ρ D a hx) hp hA
    (forall_mul_comm_quotient_subgroupOf hDcomm)
    (pow_eq_one_quotient_subgroupOf (p := p) hDpow)
  rw [hTCZ] at hTinfX
  refine ⟨X, isInvariantSubgroup_of_forall hXinv, ?_, hXD, hCX, hTX, hTinfX, ?_, ?_⟩
  · refine isCyclic_of_pow_eq_one_mem hp hodd hR hZcard fun x hx hxp => ?_
    have hxB : x ∈ B := mem_omega1_of_pow_eq_one hxp
    have hxT : x ∈ T := hBinfD ▸ Subgroup.mem_inf.2 ⟨hxB, hXD hx⟩
    exact hTinfX ▸ Subgroup.mem_inf.2 ⟨hxT, hx⟩
  · calc B ⊔ X = (B ⊔ T) ⊔ X := by rw [sup_eq_left.mpr hTB]
      _ = B ⊔ (T ⊔ X) := sup_assoc _ _ _
      _ = B ⊔ D := by rw [hTX]
      _ = ⊤ := hBDtop
  · rw [← hTinfX, ← hBinfD, inf_assoc, inf_eq_right.mpr hXD]

theorem exists_invariant_isCyclic_complement_commutator_plane_mul [Finite R] [Finite A]
    (hp : p.Prime) (hodd : Odd p) (hR : IsPGroup p R) (hB : Nat.card ↥(omega1 p R) = p ^ 3)
    (hnab : ¬ IsMulCommutative ↥(omega1 p R)) (hexp : ∀ b ∈ omega1 p R, b ^ p = 1)
    (hZ : ¬ ⁅(⊤ : Subgroup R), omega1 p R⁆
      ≤ (center ↥(omega1 p R)).map (omega1 p R).subtype)
    (ρ : A →* MulAut R) (hA : ¬ p ∣ Nat.card A) :
    ∃ X : Subgroup R, IsInvariantSubgroup ρ X ∧ IsCyclic ↥X ∧
      X ≤ centralizer ((⁅(⊤ : Subgroup R), omega1 p R⁆ : Subgroup R) : Set R) ∧
      centralizer (omega1 p R : Set R) ≤ X ∧
      ((⁅(⊤ : Subgroup R), omega1 p R⁆ : Subgroup R) : Set R) * (X : Set R)
        = (centralizer ((⁅(⊤ : Subgroup R), omega1 p R⁆ : Subgroup R) : Set R) : Set R) ∧
      ⁅(⊤ : Subgroup R), omega1 p R⁆ ⊓ X
        = (center ↥(omega1 p R)).map (omega1 p R).subtype ∧
      (omega1 p R : Set R) * (X : Set R) = Set.univ ∧
      omega1 p R ⊓ X = (center ↥(omega1 p R)).map (omega1 p R).subtype := by
  obtain ⟨X, hXinv, hXcyc, hXD, hCX, hTX, hTinfX, hBX, hBinfX⟩ :=
    exists_invariant_isCyclic_complement_commutator_plane hp hodd hR hB hnab hexp hZ ρ hA
  refine ⟨X, hXinv, hXcyc, hXD, hCX, ?_, hTinfX, ?_, hBinfX⟩
  · rw [← Subgroup.normal_mul, hTX]
  · rw [← Subgroup.normal_mul, hBX, Subgroup.coe_top]

end

end CFSG.FeitThompson
