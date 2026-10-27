module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6CtrlNDefs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Restrict
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3CenterFree
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6CtrlDefs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

namespace Sec6Fus

variable {X : Type} [Group X]

theorem orderOf_conj (g x : X) : orderOf (g * x * g⁻¹) = orderOf x := by
  have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa [MulAut.conj_apply] using h

theorem sq_eq_one_of_orderOf {x : X} (hx : orderOf x = 2) : x ^ 2 = 1 :=
  hx ▸ pow_orderOf_eq_one x

theorem isPCompIn_of_sec6KComp {n : ℕ} {H L : Subgroup X} (h : Sec6KComp X n H L) :
    IsPCompIn 2 H L := by
  rcases h with ⟨⟨u, -, -, hpc, -⟩, -⟩ | ⟨⟨hpc, -⟩, -⟩
  · exact hpc
  · exact hpc

theorem sec6K_le (n : ℕ) (H : Subgroup X) : Sec6K X n H ≤ H :=
  sSup_le fun _ hL => (isPCompIn_of_sec6KComp hL).1

theorem sec6M_le (n : ℕ) (H : Subgroup X) : Sec6M X n H ≤ H :=
  sSup_le fun _ hM => hM.1.1.1

theorem zStar_le (H : Subgroup X) : zStar H ≤ H := by
  unfold zStar
  exact inf_le_left

theorem sec6R_le (n : ℕ) (H : Subgroup X) : Sec6R X n H ≤ H :=
  sup_le ((zStar_le _).trans (K0_le n H)) (sec6M_le n H)

theorem sec6Y_le (n : ℕ) (H : Subgroup X) : Sec6Y X n H ≤ H :=
  sup_le (sec6R_le n H) ((oddCoreOf_le _).trans (sec6K_le n H))

theorem mem_normalizer_oddCoreOf_sec6K (n : ℕ) {H : Subgroup X} {c : X} (hc : c ∈ H) :
    c ∈ normalizer (oddCoreOf (Sec6K X n H) : Set X) :=
  mem_normalizer_oddCoreOf_of_mem_normalizer
    (mem_normalizer_of_map_conj_eq (map_conj_Sec6K n (Subgroup.le_normalizer hc)))

section Sylow

variable [Finite X]

private theorem card_sup_mul_card_inf_of_normal {G : Type*} [Group G] (A B : Subgroup G)
    [A.Normal] :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := A ⊔ B)
  rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [← h1, ← h2]
  ring

theorem card_sup_mul_card_inf {A B : Subgroup X} (hB : B ≤ normalizer (A : Set X)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  set N := normalizer (A : Set X)
  have hAN : A ≤ N := le_normalizer
  have : (A.subgroupOf N).Normal := normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal (A.subgroupOf N) (B.subgroupOf N)
  have hc : ∀ Y : Subgroup X, Y ≤ N → Nat.card (Y.subgroupOf N) = Nat.card Y := fun Y hY =>
    Nat.card_congr (subgroupOfEquivOfLe hY).toEquiv
  have hsup : A.subgroupOf N ⊔ B.subgroupOf N = (A ⊔ B).subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [Subgroup.map_sup, subgroupOf_map_subtype, subgroupOf_map_subtype,
      subgroupOf_map_subtype, inf_eq_left.mpr hAN, inf_eq_left.mpr hB,
      inf_eq_left.mpr (sup_le hAN hB)]
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  exact h

open scoped Pointwise in
private theorem exists_conj_mem_of_index {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ P.index) {e : G} (he : e ^ 2 = 1) :
    ∃ g : G, g * e * g⁻¹ ∈ P := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h1 : e = 1
  · exact ⟨1, by rw [h1, mul_one, inv_one, mul_one]; exact P.one_mem⟩
  have hord : orderOf e = 2 := orderOf_eq_prime he h1
  have hE : IsPGroup 2 (Subgroup.zpowers e) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q (hP.toSylow hidx)
  refine ⟨g, ?_⟩
  have h2 : MulAut.conj g • e ∈ MulAut.conj g • (Q : Subgroup G) :=
    Subgroup.smul_mem_pointwise_smul e _ _ (hQ (Subgroup.mem_zpowers e))
  rw [← Sylow.coe_subgroup_smul, hg, IsPGroup.toSylow_coe, MulAut.smul_def,
    MulAut.conj_apply] at h2
  exact h2

theorem exists_conj_mem_of_sup_odd {R O : Subgroup X} (hRO : R ≤ normalizer (O : Set X))
    (hO : Odd (Nat.card O)) {y : X} (hy : y ∈ R ⊔ O) (hy2 : y ^ 2 = 1) :
    ∃ h ∈ R ⊔ O, h * y * h⁻¹ ∈ R := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := R ⊔ O with hYdef
  have hRY : R ≤ Y := le_sup_left
  have hidxRY : ¬ 2 ∣ R.relIndex Y := by
    have h1 := Subgroup.relIndex_mul_card (H := R) (K := Y)
    rw [inf_eq_left.mpr hRY] at h1
    have h2 := card_sup_mul_card_inf hRO
    rw [sup_comm, ← hYdef, inf_comm] at h2
    have hpos : 0 < Nat.card R := Nat.card_pos
    have h3 : R.relIndex Y * Nat.card ↥(R ⊓ O) = Nat.card O := by
      have : Nat.card R * (R.relIndex Y * Nat.card ↥(R ⊓ O)) = Nat.card R * Nat.card O := by
        calc Nat.card R * (R.relIndex Y * Nat.card ↥(R ⊓ O))
            = (R.relIndex Y * Nat.card R) * Nat.card ↥(R ⊓ O) := by ring
          _ = Nat.card R * Nat.card O := by rw [h1, h2, mul_comm]
      exact Nat.eq_of_mul_eq_mul_left hpos this
    intro hdvd
    exact (Nat.not_even_iff_odd.2 hO) (even_iff_two_dvd.2 (hdvd.trans (Dvd.intro _ h3)))
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 ↥R) := inferInstance
  set P : Subgroup X := (P₀ : Subgroup ↥R).map R.subtype with hPdef
  have hPR : P ≤ R := Subgroup.map_subtype_le _
  have hPsub : P.subgroupOf R = (P₀ : Subgroup ↥R) :=
    Subgroup.comap_map_eq_self_of_injective R.subtype_injective _
  have hidxPR : ¬ 2 ∣ P.relIndex R := by
    rw [Subgroup.relIndex, hPsub]
    exact P₀.not_dvd_index
  have hidxPY : ¬ 2 ∣ P.relIndex Y := by
    rw [← Subgroup.relIndex_mul_relIndex P R Y hPR hRY]
    intro hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hdvd with h | h
    · exact hidxPR h
    · exact hidxRY h
  have hPp : IsPGroup 2 ↥(P.subgroupOf Y) := by
    have h1 : IsPGroup 2 ↥P := P₀.isPGroup'.map R.subtype
    exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe (hPR.trans hRY)).symm
  obtain ⟨g, hg⟩ := exists_conj_mem_of_index hPp hidxPY
    (e := (⟨y, hy⟩ : ↥Y)) (Subtype.ext (by simpa using hy2))
  refine ⟨(g : X), g.2, hPR ?_⟩
  have := Subgroup.mem_subgroupOf.1 hg
  simpa using this

end Sylow

section Solvable

variable [Finite X]

theorem exists_mul_of_mem_sup {H K : Subgroup X} (hH : H ≤ normalizer (K : Set X)) {x : X}
    (hx : x ∈ H ⊔ K) : ∃ y ∈ H, ∃ z ∈ K, y * z = x := by
  have h : x ∈ ((H ⊔ K : Subgroup X) : Set X) := hx
  rw [coe_mul_of_left_le_normalizer_right H K hH] at h
  obtain ⟨y, hy, z, hz, rfl⟩ := h
  exact ⟨y, hy, z, hz, rfl⟩

theorem isSolvable_sup_of_le_normalizer {T D : Subgroup X}
    (hD : D ≤ normalizer (T : Set X)) (hT : Group.IsSolvable T)
    (hD' : Group.IsSolvable D) : Group.IsSolvable ↥(D ⊔ T) := by
  have hnorm : (T.subgroupOf (D ⊔ T)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hD
  have hnormD : (T.subgroupOf D).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hD
  have hker : (QuotientGroup.mk' (T.subgroupOf (D ⊔ T))).ker ≤
      (T.subgroupOf (D ⊔ T)).subtype.range := by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype]
  let e₁ := Subgroup.subgroupOfEquivOfLe (le_sup_right : T ≤ D ⊔ T)
  have h1 : Group.IsSolvable ↥(T.subgroupOf (D ⊔ T)) :=
    Group.isSolvable_of_surjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective
  let e₂ := QuotientGroup.quotientInfEquivProdNormalizerQuotient D T hD
  have h2 : Group.IsSolvable (↥(D ⊔ T) ⧸ T.subgroupOf (D ⊔ T)) := by
    have : Group.IsSolvable (↥D ⧸ T.subgroupOf D) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
    exact Group.isSolvable_of_surjective (f := e₂.toMonoidHom) e₂.surjective
  exact Group.isSolvable_of_ker_le_range _ _ hker

theorem isSolvable_of_le {A B : Subgroup X} (hAB : A ≤ B) (hB : Group.IsSolvable ↥B) :
    Group.IsSolvable ↥A :=
  Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hAB)
    (Subgroup.inclusion_injective hAB)

theorem isSolvable_of_odd {A : Subgroup X} (hA : Odd (Nat.card A)) : Group.IsSolvable ↥A :=
  CFSG.FeitThompson.isSolvable_of_odd_natCard _ hA

theorem isSolvable_sup_odd {T D : Subgroup X} (hD : D ≤ normalizer (T : Set X))
    (hT : Odd (Nat.card T)) (hD' : Group.IsSolvable D) : Group.IsSolvable ↥(D ⊔ T) :=
  isSolvable_sup_of_le_normalizer hD (isSolvable_of_odd hT) hD'

omit [Finite X] in
theorem not_isSolvable_cen_conj {y : X} (g : X) (h : ¬ Group.IsSolvable ↥(cen y)) :
    ¬ Group.IsSolvable ↥(cen (g * y * g⁻¹)) := by
  intro hs
  apply h
  let φ : ↥(cen y) →* ↥(cen (g * y * g⁻¹)) :=
    { toFun := fun c => ⟨g * c * g⁻¹, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hc : (c : X) * y = y * c := Subgroup.mem_centralizer_singleton_iff.1 c.2
        calc g * c * g⁻¹ * (g * y * g⁻¹) = g * ((c : X) * y) * g⁻¹ := by group
          _ = g * (y * c) * g⁻¹ := by rw [hc]
          _ = g * y * g⁻¹ * (g * c * g⁻¹) := by group⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 : g * (a : X) * g⁻¹ = g * b * g⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (by simpa using h1)
  exact Group.isSolvable_of_isSolvable_injective hφ

omit [Group X] in
private theorem exists_fixed_of_involutive {f : X → X} (hf : Function.Involutive f)
    (hX : Odd (Nat.card X)) : ∃ x, f x = x := by
  classical
  have := Fintype.ofFinite X
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ : hf.toPerm f ^ 2 ^ 1 = 1 := by
    ext x
    simp [sq, hf x]
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2)
    (by rw [← Nat.card_eq_fintype_card]; exact hX.not_two_dvd_nat) hσ
  exact ⟨x, hx⟩

theorem exists_mul_mem_cen_of_coset {O : Subgroup X} (hO : Odd (Nat.card O)) {r c : X}
    (hr : r * r = 1) (hrO : r ∈ normalizer (O : Set X)) (hc : c⁻¹ * (r * c * r⁻¹) ∈ O) :
    ∃ o ∈ O, c * o ∈ cen r := by
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
  have hmem : ∀ o ∈ O, c⁻¹ * (r * (c * o) * r⁻¹) ∈ O := fun o ho => by
    have h1 : r * o * r⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 hrO o).1 ho
    have e : c⁻¹ * (r * (c * o) * r⁻¹) = (c⁻¹ * (r * c * r⁻¹)) * (r * o * r⁻¹) := by group
    rw [e]
    exact O.mul_mem hc h1
  let φ : ↥O → ↥O := fun o => ⟨c⁻¹ * (r * (c * o) * r⁻¹), hmem o o.2⟩
  have hφ : Function.Involutive φ := by
    intro o
    apply Subtype.ext
    show c⁻¹ * (r * (c * (c⁻¹ * (r * (c * (o : X)) * r⁻¹))) * r⁻¹) = o
    calc c⁻¹ * (r * (c * (c⁻¹ * (r * (c * (o : X)) * r⁻¹))) * r⁻¹)
        = c⁻¹ * ((r * r) * (c * o) * (r⁻¹ * r⁻¹)) := by group
      _ = o := by rw [hri, hr]; group
  obtain ⟨o, ho⟩ := exists_fixed_of_involutive hφ hO
  refine ⟨o, o.2, ?_⟩
  have h : c⁻¹ * (r * (c * (o : X)) * r⁻¹) = o := congrArg Subtype.val ho
  have h' : r * (c * (o : X)) * r⁻¹ = c * o := by
    calc r * (c * (o : X)) * r⁻¹ = c * (c⁻¹ * (r * (c * (o : X)) * r⁻¹)) := by group
      _ = c * o := by rw [h]
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc c * (o : X) * r = r * (c * o) * r⁻¹ * r := by rw [h']
    _ = r * (c * o) := by group

end Solvable

section Components

private theorem conj_mem_of_comm_mem {M : Subgroup X} {g : X} (hg : ∀ m ∈ M, ⁅m, g⁆ ∈ M)
    {x : X} (hx : x ∈ M) : g * x * g⁻¹ ∈ M := by
  have h1 := M.mul_mem hx (hg x⁻¹ (M.inv_mem hx))
  have h2 : x * ⁅x⁻¹, g⁆ = g * x * g⁻¹ := by
    rw [commutatorElement_def]
    group
  rwa [h2] at h1

private theorem mem_normalizer_of_comm_mem {M : Subgroup X} {j : X} (h : ∀ m ∈ M, ⁅m, j⁆ ∈ M)
    (h' : ∀ m ∈ M, ⁅m, j⁻¹⁆ ∈ M) : j ∈ normalizer (M : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_of_comm_mem h, fun hx => ?_⟩
  have := conj_mem_of_comm_mem h' hx
  rwa [show j⁻¹ * (j * x * j⁻¹) * j⁻¹⁻¹ = x by group] at this

variable [Finite X]

theorem commutatorElement_mem_of_ne {H M J : Subgroup X} (hM : IsPCompIn 2 H M)
    (hJ : IsPCompIn 2 H J) (hne : M ≠ J) {m j : X} (hm : m ∈ M) (hj : j ∈ J) :
    ⁅m, j⁆ ∈ oddCoreOf M := by
  have hne' : M.subgroupOf H ≠ J.subgroupOf H := by
    intro h
    apply hne
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hM.1, inf_of_le_left hJ.1] at h
    exact h
  obtain ⟨-, -, hcore, -⟩ :=
    (ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation 2
      Nat.prime_two _ _ hM.2 hJ.2).2 hne'
  have hc : ⁅(⟨m, hM.1 hm⟩ : ↥H), (⟨j, hJ.1 hj⟩ : ↥H)⁆ ∈
      (pPrimeCore 2 ↥(M.subgroupOf H)).map (M.subgroupOf H).subtype :=
    (hcore.trans inf_le_left) (Subgroup.commutator_mem_commutator hm hj)
  obtain ⟨y, hy, hyeq⟩ := hc
  let e : ↥(M.subgroupOf H) ≃* ↥M := Subgroup.subgroupOfEquivOfLe hM.1
  have hey : e y ∈ pPrimeCore 2 ↥M := by
    rw [← pPrimeCore_map_iso 2 e]
    exact ⟨y, hy, rfl⟩
  refine ⟨e y, hey, ?_⟩
  change ((y : ↥H) : X) = ⁅m, j⁆
  exact congrArg Subtype.val hyeq

theorem le_QOf_of_ne {H M J : Subgroup X} (hM : IsPCompIn 2 H M) (hJ : IsPCompIn 2 H J)
    (hne : M ≠ J) : J ≤ QOf M := by
  intro j hj
  have hOMM : oddCoreOf M ≤ M := oddCoreOf_le M
  have hc : ∀ g ∈ J, ∀ m ∈ M, ⁅m, g⁆ ∈ oddCoreOf M := fun g hg m hm =>
    commutatorElement_mem_of_ne hM hJ hne hm hg
  exact mem_QOf_iff.2 ⟨mem_normalizer_of_comm_mem (fun m hm => hOMM (hc j hj m hm))
    (fun m hm => hOMM (hc j⁻¹ (J.inv_mem hj) m hm)), fun m hm => hc j hj m hm⟩

theorem sSup_le_normalizer {H M : Subgroup X} {S : Set (Subgroup X)} (hM : IsPCompIn 2 H M)
    (hS : ∀ J ∈ S, IsPCompIn 2 H J) : sSup S ≤ normalizer (M : Set X) := by
  refine sSup_le fun J hJ => ?_
  by_cases hne : M = J
  · rw [← hne]
    exact Subgroup.le_normalizer
  exact (le_QOf_of_ne hM (hS J hJ) hne).trans fun q hq => (mem_QOf_iff.1 hq).1

theorem conj_mem_QOf {A : Subgroup X} {c q : X} (hc : c ∈ normalizer (A : Set X))
    (hq : q ∈ QOf A) : c * q * c⁻¹ ∈ QOf A := by
  have hcO := mem_normalizer_oddCoreOf_of_mem_normalizer hc
  obtain ⟨hqA, hqc⟩ := mem_QOf_iff.1 hq
  refine mem_QOf_iff.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hqA) (Subgroup.inv_mem _ hc),
    fun a ha => ?_⟩
  have ha' : c⁻¹ * a * c ∈ A := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hc) a).1 ha
    rwa [inv_inv] at this
  have h2 : c * ⁅c⁻¹ * a * c, q⁆ * c⁻¹ ∈ oddCoreOf A :=
    (Subgroup.mem_normalizer_iff.1 hcO _).1 (hqc _ ha')
  have e : ⁅a, c * q * c⁻¹⁆ = c * ⁅c⁻¹ * a * c, q⁆ * c⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact h2

theorem mem_normalizer_QOf {A : Subgroup X} {c : X} (hc : c ∈ normalizer (A : Set X)) :
    c ∈ normalizer (QOf A : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro q
  refine ⟨conj_mem_QOf hc, fun h => ?_⟩
  have := conj_mem_QOf (Subgroup.inv_mem _ hc) h
  rwa [show c⁻¹ * (c * q * c⁻¹) * c⁻¹⁻¹ = q by group] at this

theorem ne_of_sec5Comp_of_sec6MComp (hcf : McLLyCenterFree) {n : ℕ} {H A M : Subgroup X}
    (hA : Sec5Comp X n H A) (hM : Sec6MComp X n H M) : A ≠ M := by
  rintro rfl
  have hZ := hcf _ hM.1.2.1
  have h2 := hA.2.2.1
  rw [hZ, Subgroup.card_bot] at h2
  exact absurd h2 (by decide)

end Components

section NonSolvable

variable [Finite X]

theorem oTwoPrimeOf_le (K : Subgroup X) : oTwoPrimeOf K ≤ K :=
  (Subgroup.closure_le K).2 fun _ hx => hx.1

theorem oddCoreOf_le_QOf (F : Subgroup X) : oddCoreOf F ≤ QOf F := by
  intro o ho
  have hoF : o ∈ F := oddCoreOf_le F ho
  refine mem_QOf_iff.2 ⟨Subgroup.le_normalizer hoF, fun a ha => ?_⟩
  have h1 : a * o * a⁻¹ ∈ oddCoreOf F :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf F ha) o).1 ho
  rw [commutatorElement_def]
  exact (oddCoreOf F).mul_mem h1 ((oddCoreOf F).inv_mem ho)

theorem zStar_le_oddCoreOf_of_center {F : Subgroup X}
    (hZ : center (↥F ⧸ pPrimeCore 2 ↥F) = ⊥) : zStar F ≤ oddCoreOf F := by
  rintro z ⟨hzF, -, -, hz⟩
  have hmem : ((⟨z, hzF⟩ : ↥F) : ↥F ⧸ pPrimeCore 2 ↥F) ∈ center (↥F ⧸ pPrimeCore 2 ↥F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨w, hw, hweq⟩ := hz a a.2
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hw' : (a * ⟨z, hzF⟩)⁻¹ * w⁻¹ * (a * ⟨z, hzF⟩) ∈ pPrimeCore 2 ↥F := by
      have hn : (pPrimeCore 2 ↥F).Normal := inferInstance
      have := hn.conj_mem _ ((pPrimeCore 2 ↥F).inv_mem hw) (a * ⟨z, hzF⟩)⁻¹
      simpa only [inv_inv] using this
    convert hw' using 1
    apply Subtype.ext
    have hweq' : (w : X) = (a : X) * z * (a : X)⁻¹ * z⁻¹ := by
      rw [← commutatorElement_def]
      exact hweq
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hweq']
    group
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
  exact ⟨_, hmem, rfl⟩

theorem not_isSolvable_inf_cen_of_mem_QOf {H L : Subgroup X} (hL : IsPCompIn 2 H L) {r : X}
    (hr2 : r ^ 2 = 1) (hr : r ∈ QOf L) : ¬ Group.IsSolvable ↥(L ⊓ cen r) := by
  have hpc := (isPCompIn_restrict hL hr2 hr).1
  have hq : IsTwoGenQuasi ↥(oTwoPrimeOf (L ⊓ cen r)) :=
    (isTwoGenQuasi_subgroupOf_iff hpc.1).1 (isPComponent_two_iff.1 hpc.2).2
  exact fun hs => not_isSolvable_of_isTwoGenQuasi hq (isSolvable_of_le (oTwoPrimeOf_le _) hs)

theorem not_isSolvable_inf_cen_of_isMLIntrIn (hcf : McLLyCenterFree) {H F : Subgroup X}
    (hF : IsMLIntrIn X H F) {r : X} (hr2 : r ^ 2 = 1) (hrF : r ∈ QOf F ⊔ F) :
    ¬ Group.IsSolvable ↥(F ⊓ cen r) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := oddCoreOf F with hOdef
  have hOodd : Odd (Nat.card O) := odd_card_oddCoreOf F
  have hOF : O ≤ F := oddCoreOf_le F
  have hFnO : F ≤ normalizer (O : Set X) := le_normalizer_oddCoreOf F
  have hQnF : QOf F ≤ normalizer (F : Set X) := fun q hq => (mem_QOf_iff.1 hq).1
  obtain ⟨q, hq, f, hf, rfl⟩ := exists_mul_of_mem_sup hQnF hrF
  by_cases hfQ : f ∈ QOf F
  · exact not_isSolvable_inf_cen_of_mem_QOf hF.1 hr2 ((QOf F).mul_mem hq hfQ)
  have hqO : q ∈ normalizer (O : Set X) := mem_normalizer_oddCoreOf_of_mem_normalizer (hQnF hq)
  have hqc : ∀ a ∈ F, ⁅a, q⁆ ∈ O := (mem_QOf_iff.1 hq).2
  have hconjO : ∀ {g o : X}, g ∈ normalizer (O : Set X) → o ∈ O → g * o * g⁻¹ ∈ O :=
    fun hg ho => (Subgroup.mem_normalizer_iff.1 hg _).1 ho
  have hconjO' : ∀ {g o : X}, g ∈ normalizer (O : Set X) → o ∈ O → g⁻¹ * o * g ∈ O :=
    fun hg ho => by
      have := hconjO (Subgroup.inv_mem _ hg) ho
      rwa [inv_inv] at this
  have hZ : center (↥F ⧸ pPrimeCore 2 ↥F) = ⊥ := hcf _ hF.2.1
  have ho1 : ⁅f, q⁆ ∈ O := hqc f hf
  have hq2 : q * q = f⁻¹ * ⁅f, q⁆ * f⁻¹ := by
    have hr' : q * f * (q * f) = 1 := by rw [← sq]; exact hr2
    have h1 : f * q * f * q = 1 := by
      calc f * q * f * q = q⁻¹ * (q * f * (q * f)) * q := by group
        _ = 1 := by rw [hr']; group
    have hfqf : f * q * f = q⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [commutatorElement_def]
    calc q * q = q * f⁻¹ * (f * q * f) * f⁻¹ := by group
      _ = q * f⁻¹ * q⁻¹ * f⁻¹ := by rw [hfqf]
      _ = f⁻¹ * (f * q * f⁻¹ * q⁻¹) * f⁻¹ := by group
  have hq2F : q * q ∈ F := by
    rw [hq2]
    exact F.mul_mem (F.mul_mem (F.inv_mem hf) (hOF ho1)) (F.inv_mem hf)
  have hq2O : q * q ∈ O := zStar_le_oddCoreOf_of_center hZ ⟨hq2F, (QOf F).mul_mem hq hq⟩
  have hf2 : f * f ∈ O := by
    have h1 : f⁻¹ * ⁅f, q⁆ * f⁻¹ ∈ O := hq2 ▸ hq2O
    have h2 : f⁻¹ * ⁅f, q⁆ * f ∈ O := hconjO' (hFnO hf) ho1
    have h3 : (f * f)⁻¹ = (f⁻¹ * ⁅f, q⁆ * f)⁻¹ * (f⁻¹ * ⁅f, q⁆ * f⁻¹) := by group
    have h4 : (f * f)⁻¹ ∈ O := h3 ▸ O.mul_mem (O.inv_mem h2) h1
    have h5 := O.inv_mem h4
    rwa [inv_inv] at h5
  obtain ⟨k, hk⟩ := id hOodd
  set s := f ^ Nat.card O with hsdef
  have hsF : s ∈ F := F.pow_mem hf _
  have hf2k : (f * f) ^ k ∈ O := O.pow_mem hf2 k
  have hs_eq : s = f * (f * f) ^ k := by
    rw [hsdef, hk, pow_succ', ← sq, ← pow_mul]
  have hs2 : s ^ 2 = 1 := by
    have h2 : (f * f) ^ Nat.card O = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard O hf2)
    rw [hsdef, ← pow_mul, mul_comm, pow_mul, sq]
    exact h2
  have hs1 : s ≠ 1 := by
    intro h1
    apply hfQ
    have hf' : f = ((f * f) ^ k)⁻¹ := by
      rw [hs_eq] at h1
      exact eq_inv_of_mul_eq_one_left h1
    rw [hf']
    exact oddCoreOf_le_QOf F (O.inv_mem hf2k)
  have hsord : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  obtain ⟨J, hJ, hJle⟩ := hF.2.2 s hsF hsord
  intro hsol
  have hsub : F ⊓ cen s ≤ (F ⊓ cen (q * f)) ⊔ O := by
    rintro c ⟨hcF, hcs⟩
    have hcs' : c * s = s * c := Subgroup.mem_centralizer_singleton_iff.1 hcs
    have hcs'' : c⁻¹ * s = s * c⁻¹ := by
      calc c⁻¹ * s = c⁻¹ * (s * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * s) * c⁻¹ := by rw [hcs']
        _ = s * c⁻¹ := by group
    set o₀ := (f * f) ^ k with ho₀
    have hfs : f = s * o₀⁻¹ := by rw [hs_eq]; group
    have hw : c⁻¹ * (f * c * f⁻¹) ∈ O := by
      have e : c⁻¹ * (f * c * f⁻¹) = s * ((c⁻¹ * o₀⁻¹ * c) * o₀) * s⁻¹ := by
        calc c⁻¹ * (f * c * f⁻¹) = (c⁻¹ * s) * (o₀⁻¹ * c * o₀ * s⁻¹) := by rw [hfs]; group
          _ = (s * c⁻¹) * (o₀⁻¹ * c * o₀ * s⁻¹) := by rw [hcs'']
          _ = s * ((c⁻¹ * o₀⁻¹ * c) * o₀) * s⁻¹ := by group
      rw [e]
      refine hconjO (hFnO hsF) (O.mul_mem ?_ hf2k)
      exact hconjO' (hFnO hcF) (O.inv_mem hf2k)
    have hcoset : c⁻¹ * (q * f * c * (q * f)⁻¹) ∈ O := by
      have e : c⁻¹ * (q * f * c * (q * f)⁻¹) =
          ⁅c⁻¹, q⁆ * (q * (c⁻¹ * (f * c * f⁻¹)) * q⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact O.mul_mem (hqc _ (F.inv_mem hcF)) (hconjO hqO hw)
    have hr' : q * f * (q * f) = 1 := by rw [← sq]; exact hr2
    obtain ⟨o, ho, hco⟩ := exists_mul_mem_cen_of_coset hOodd hr'
      (Subgroup.mul_mem _ hqO (hFnO hf)) hcoset
    have hc : c = (c * o) * o⁻¹ := by group
    rw [hc]
    exact Subgroup.mul_mem _ (le_sup_left (a := F ⊓ cen (q * f))
      ⟨F.mul_mem hcF (hOF ho), hco⟩) (le_sup_right (a := F ⊓ cen (q * f)) (O.inv_mem ho))
  have hsol1 : Group.IsSolvable ↥((F ⊓ cen (q * f)) ⊔ O) :=
    isSolvable_sup_odd (fun x hx => hFnO hx.1) hOodd hsol
  have hsol2 : Group.IsSolvable ↥(F ⊓ cen s) := isSolvable_of_le hsub hsol1
  have hsol3 : Group.IsSolvable ↥((F ⊓ cen s) ⊔ oddCoreOf (cen s)) :=
    isSolvable_sup_odd (fun x hx => le_normalizer_oddCoreOf (cen s) hx.2)
      (odd_card_oddCoreOf _) hsol2
  exact not_isSolvable_of_isTwoGenQuasi (isTwoGenQuasi_of_isAhatIntr hJ)
    (isSolvable_of_le hJle hsol3)

end NonSolvable

section StepTwoD

variable [Finite X]

private theorem normal_le_center_or_eq_top {K : Type*} [Group K] (hq : IsQuasisimple K)
    (M : Subgroup K) [M.Normal] : M ≤ Subgroup.center K ∨ M = ⊤ := by
  obtain ⟨hperf, hs, -⟩ := hq
  have hnorm : (M.map (QuotientGroup.mk' (Subgroup.center K))).Normal :=
    Subgroup.Normal.map ‹M.Normal› (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have := hnorm
  rcases hs.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' (Subgroup.center K))) with h | h
  · left
    intro m hm
    have h1 : QuotientGroup.mk' (Subgroup.center K) m ∈
        M.map (QuotientGroup.mk' (Subgroup.center K)) := Subgroup.mem_map_of_mem _ hm
    rw [h, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff m).mp h1
  · right
    have hsup : M ⊔ Subgroup.center K = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center K)) M
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hle : commutator K ≤ M :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [Group.isPerfect_def.mp hperf] at hle
    exact top_le_iff.mp hle

theorem mem_zStar_of_mk_mem_center {A : Subgroup X} {a : X} (ha : a ∈ A)
    (h : ((⟨a, ha⟩ : ↥A) : ↥A ⧸ pPrimeCore 2 ↥A) ∈ center (↥A ⧸ pPrimeCore 2 ↥A)) :
    a ∈ zStar A := by
  refine ⟨ha, Subgroup.le_normalizer ha, le_normalizer_oddCoreOf A ha, fun k hk => ?_⟩
  have hc := Subgroup.mem_center_iff.1 h ((⟨k, hk⟩ : ↥A) : ↥A ⧸ pPrimeCore 2 ↥A)
  have hmem : ⁅k, a⁆ ∈ A := by
    rw [commutatorElement_def]
    exact A.mul_mem (A.mul_mem (A.mul_mem hk ha) (A.inv_mem hk)) (A.inv_mem ha)
  have h1 : (⟨⁅k, a⁆, hmem⟩ : ↥A) ∈ pPrimeCore 2 ↥A := by
    rw [← QuotientGroup.eq_one_iff]
    have e : (⟨⁅k, a⁆, hmem⟩ : ↥A) = ⟨k, hk⟩ * ⟨a, ha⟩ * (⟨k, hk⟩ : ↥A)⁻¹ * (⟨a, ha⟩ : ↥A)⁻¹ :=
      Subtype.ext (by simp [commutatorElement_def])
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hc]
    group
  exact ⟨_, h1, rfl⟩

theorem relIndex_zStar_le (A : Subgroup X) :
    (zStar A).relIndex A ≤ Nat.card ((↥A ⧸ pPrimeCore 2 ↥A) ⧸ center (↥A ⧸ pPrimeCore 2 ↥A)) := by
  set C := (center (↥A ⧸ pPrimeCore 2 ↥A)).comap (QuotientGroup.mk' (pPrimeCore 2 ↥A))
  have hC : C ≤ (zStar A).subgroupOf A := fun a ha => mem_zStar_of_mk_mem_center a.2 ha
  have h1 : ((zStar A).subgroupOf A).index ∣ C.index := Subgroup.index_dvd_of_le hC
  have h2 : C.index = (center (↥A ⧸ pPrimeCore 2 ↥A)).index :=
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h3 : C.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [Subgroup.relIndex]
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero h3) h1).trans h2.le

theorem card_quot_center_le_relIndex {J K : Subgroup X} (hJ : IsTwoGenQuasi ↥J) (hKJ : K ≤ J)
    (hn : J ≤ normalizer (K : Set X)) (hne : ¬ J ≤ K) :
    Nat.card ((↥J ⧸ pPrimeCore 2 ↥J) ⧸ center (↥J ⧸ pPrimeCore 2 ↥J)) ≤ K.relIndex J := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K' := K.subgroupOf J with hK'
  haveI hK'n : K'.Normal := (normal_subgroupOf_iff_le_normalizer hKJ).2 hn
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥J) with hπ
  haveI : (K'.map π).Normal := Subgroup.Normal.map hK'n π (QuotientGroup.mk'_surjective _)
  rcases normal_le_center_or_eq_top hJ.2 (K'.map π) with hc | ht
  · have hle : K' ≤ (center (↥J ⧸ pPrimeCore 2 ↥J)).comap π := Subgroup.map_le_iff_le_comap.1 hc
    have h1 : ((center (↥J ⧸ pPrimeCore 2 ↥J)).comap π).index ∣ K'.index :=
      Subgroup.index_dvd_of_le hle
    have h2 : ((center (↥J ⧸ pPrimeCore 2 ↥J)).comap π).index =
        (center (↥J ⧸ pPrimeCore 2 ↥J)).index :=
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
    rw [Subgroup.relIndex, ← hK']
    exact h2.symm.le.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1)
  · exfalso
    apply hne
    have hsup : K' ⊔ pPrimeCore 2 ↥J = ⊤ := by
      have h := Subgroup.comap_map_eq π K'
      rw [ht, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
      exact h.symm
    have hcop : Nat.Coprime 2 K'.index := by
      have h1 : K'.index = K'.relIndex (pPrimeCore 2 ↥J) := by
        rw [← Subgroup.relIndex_sup_right (H := pPrimeCore 2 ↥J) (K := K'), sup_comm, hsup,
          Subgroup.relIndex_top_right]
      have h2 : K'.relIndex (pPrimeCore 2 ↥J) ∣ Nat.card (pPrimeCore 2 ↥J) :=
        Dvd.intro _ (Subgroup.relIndex_mul_card (H := K') (K := pPrimeCore 2 ↥J))
      rw [h1]
      exact Nat.Coprime.coprime_dvd_right h2 pPrimeCore_coprime_card
    have hres :=
      ComponentClassification.CatalogueBPrimeJoin.primeResidual_le_normal_of_coprime_index
        2 K' hcop
    rw [hJ.1] at hres
    intro x hx
    exact hres (Subgroup.mem_top (⟨x, hx⟩ : ↥J))

theorem mem_QOf_of_commutator_mem_zStar {A : Subgroup X} (hA : IsTwoGenQuasi ↥A) {x : X}
    (hxA : x ∈ normalizer (A : Set X)) (h : ∀ a ∈ A, ⁅a, x⁆ ∈ zStar A) : x ∈ QOf A := by
  set Q := ↥A ⧸ pPrimeCore 2 ↥A
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥A)
  have hxO : x ∈ normalizer (oddCoreOf A : Set X) := mem_normalizer_oddCoreOf_of_mem_normalizer hxA
  have hmemA : ∀ a : ↥A, ⁅(a : X), x⁆ ∈ A := fun a => zStar_le A (h a a.2)
  have hcent : ∀ a : ↥A, π ⟨⁅(a : X), x⁆, hmemA a⟩ ∈ center Q := by
    intro a
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨-, -, -, hz⟩ := h a a.2
    obtain ⟨w, hw, hweq⟩ := hz k k.2
    change (k : Q) * (⟨⁅(a : X), x⁆, hmemA a⟩ : ↥A) = (⟨⁅(a : X), x⁆, hmemA a⟩ : ↥A) * (k : Q)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hn : (pPrimeCore 2 ↥A).Normal := inferInstance
    have hw' := hn.conj_mem _ ((pPrimeCore 2 ↥A).inv_mem hw)
      (k * ⟨⁅(a : X), x⁆, hmemA a⟩)⁻¹
    rw [inv_inv] at hw'
    convert hw' using 1
    apply Subtype.ext
    have hweq' : (w : X) = (k : X) * ⁅(a : X), x⁆ * (k : X)⁻¹ * ⁅(a : X), x⁆⁻¹ := by
      rw [← commutatorElement_def]
      exact hweq
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hweq']
    group
  let ψ : ↥A →* ↥(center Q) :=
    { toFun := fun a => ⟨π ⟨⁅(a : X), x⁆, hmemA a⟩, hcent a⟩
      map_one' := by
        apply Subtype.ext
        change π ⟨⁅((1 : ↥A) : X), x⁆, hmemA 1⟩ = 1
        have e : (⟨⁅((1 : ↥A) : X), x⁆, hmemA 1⟩ : ↥A) = 1 := Subtype.ext (by simp)
        rw [e, map_one]
      map_mul' := by
        intro a b
        apply Subtype.ext
        change π ⟨⁅((a * b : ↥A) : X), x⁆, hmemA (a * b)⟩ =
          π ⟨⁅(a : X), x⁆, hmemA a⟩ * π ⟨⁅(b : X), x⁆, hmemA b⟩
        have e : (⟨⁅((a * b : ↥A) : X), x⁆, hmemA (a * b)⟩ : ↥A) =
            a * ⟨⁅(b : X), x⁆, hmemA b⟩ * a⁻¹ * ⟨⁅(a : X), x⁆, hmemA a⟩ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
          group
        rw [e, map_mul, map_mul, map_mul, map_inv]
        have hc := Subgroup.mem_center_iff.1 (hcent b) (π a)
        rw [hc, mul_inv_cancel_right]
        exact Subgroup.mem_center_iff.1 (hcent a) _ }
  have hker : ∀ o ∈ pPrimeCore 2 ↥A, ψ o = 1 := by
    intro o ho
    apply Subtype.ext
    change π ⟨⁅(o : X), x⁆, hmemA o⟩ = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hoO : (o : X) ∈ oddCoreOf A := ⟨o, ho, rfl⟩
    have h1 : x * (o : X)⁻¹ * x⁻¹ ∈ oddCoreOf A :=
      (Subgroup.mem_normalizer_iff.1 hxO _).1 ((oddCoreOf A).inv_mem hoO)
    have h2 : ⁅(o : X), x⁆ ∈ oddCoreOf A := by
      rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc x]
      exact (oddCoreOf A).mul_mem hoO h1
    obtain ⟨w, hw, hweq⟩ := h2
    have : (⟨⁅(o : X), x⁆, hmemA o⟩ : ↥A) = w := Subtype.ext hweq.symm
    rw [this]
    exact hw
  let ψ' : Q →* ↥(center Q) := QuotientGroup.lift (pPrimeCore 2 ↥A) ψ hker
  have hall : ∀ q : Q, ψ' q = 1 := by
    intro q
    have h1 : commutator Q ≤ ψ'.ker := Abelianization.commutator_subset_ker ψ'
    rw [Group.isPerfect_def.mp hA.2.1] at h1
    exact h1 (Subgroup.mem_top q)
  refine mem_QOf_iff.2 ⟨hxA, fun a ha => ?_⟩
  have h1 : ψ ⟨a, ha⟩ = 1 := hall (π ⟨a, ha⟩)
  have h2 : π ⟨⁅a, x⁆, hmemA ⟨a, ha⟩⟩ = 1 := congrArg Subtype.val h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact ⟨_, h2, rfl⟩

theorem card_alt_le_of_sec6KComp
    (hcf : McLLyCenterFree) {n : ℕ} {H J : Subgroup X} (hJ : Sec6KComp X n H J) :
    Nat.card (alternatingGroup (Fin n)) ≤
      Nat.card ((↥J ⧸ pPrimeCore 2 ↥J) ⧸ center (↥J ⧸ pPrimeCore 2 ↥J)) := by
  rcases hJ with hJ | hJ
  · obtain ⟨-, -, ⟨e⟩⟩ := hJ.2
    exact (Nat.card_congr e.toEquiv).symm.le
  · have hZ := hcf _ hJ.1.2.1
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (center (↥J ⧸ pPrimeCore 2 ↥J))
    have h1' : Nat.card ↥(center (↥J ⧸ pPrimeCore 2 ↥J)) = 1 := by rw [hZ, Subgroup.card_bot]
    rw [h1', mul_one] at h1
    rw [← h1]
    rcases hJ.2 with ⟨rfl, ⟨e⟩⟩ | ⟨rfl, ⟨e⟩⟩
    · rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.McL.card_McL, nat_card_alternatingGroup,
        Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num [Nat.factorial]
    · rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Ly.card_Ly', nat_card_alternatingGroup,
        Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num [Nat.factorial]

theorem mem_QOf_of_mem_sec6K
    (hcf : McLLyCenterFree) {n : ℕ} {N H : Subgroup X} {x : X} (hH : H ≤ cen x)
    (hxK : x ∈ Sec6K X n H) (hKx : Sec6K X n H ≤ Sec6K X n N) {A : Subgroup X}
    (hA : Sec5Comp X n N A) : x ∈ QOf A := by
  by_contra hxQ
  set Q := QOf A with hQdef
  have hApc : IsPCompIn 2 N A := isPCompIn_of_sec6KComp (Or.inl hA)
  have hAq : IsTwoGenQuasi ↥A :=
    (isTwoGenQuasi_subgroupOf_iff hApc.1).1 (isPComponent_two_iff.1 hApc.2).2
  have hKnA : Sec6K X n N ≤ normalizer (A : Set X) :=
    sSup_le_normalizer hApc fun J hJ => isPCompIn_of_sec6KComp hJ
  have hxKN : x ∈ Sec6K X n N := hKx hxK
  have hxA : x ∈ normalizer (A : Set X) := hKnA hxKN
  obtain ⟨a, haA, hax⟩ : ∃ a ∈ A, ⁅a, x⁆ ∉ zStar A := by
    by_contra hno
    push Not at hno
    exact hxQ (mem_QOf_of_commutator_mem_zStar hAq hxA hno)
  have hKG : Sec6K X n N ≤ A ⊔ Q := sSup_le fun L hL => by
    by_cases hAL : A = L
    · rw [← hAL]
      exact le_sup_left
    · exact (le_QOf_of_ne hApc (isPCompIn_of_sec6KComp hL) hAL).trans le_sup_right
  set G₀ := A ⊔ Q with hG₀
  have hQG : Q ≤ G₀ := le_sup_right
  have hAG : A ≤ G₀ := le_sup_left
  have hG₀Q : G₀ ≤ normalizer (Q : Set X) :=
    sup_le (fun c hc => mem_normalizer_QOf (Subgroup.le_normalizer hc)) Subgroup.le_normalizer
  haveI hQn : (Q.subgroupOf G₀).Normal := (normal_subgroupOf_iff_le_normalizer hQG).2 hG₀Q
  set π₀ := QuotientGroup.mk' (Q.subgroupOf G₀) with hπ₀
  have hxG : x ∈ G₀ := hKG hxKN
  set C₀ := (centralizer ({π₀ ⟨x, hxG⟩} : Set (↥G₀ ⧸ Q.subgroupOf G₀))).comap π₀ with hC₀def
  have hQC : Q.subgroupOf G₀ ≤ C₀ := fun q hq => by
    have h1 : π₀ q = 1 := (QuotientGroup.eq_one_iff q).2 hq
    show π₀ q ∈ centralizer _
    rw [h1]
    exact one_mem _
  have hC₀ : C₀ ≠ ⊤ := by
    intro htop
    have h1 : (⟨a, hAG haA⟩ : ↥G₀) ∈ C₀ := htop ▸ Subgroup.mem_top _
    have h2 : π₀ ⟨a, hAG haA⟩ * π₀ ⟨x, hxG⟩ = π₀ ⟨x, hxG⟩ * π₀ ⟨a, hAG haA⟩ :=
      Subgroup.mem_centralizer_singleton_iff.1 h1
    have h3 : ⁅a, x⁆ ∈ Q := by
      have h4 : π₀ (⟨a, hAG haA⟩ * ⟨x, hxG⟩ * (⟨a, hAG haA⟩ : ↥G₀)⁻¹ * (⟨x, hxG⟩ : ↥G₀)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h2]
        group
      rw [hπ₀, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h4
      have := Subgroup.mem_subgroupOf.1 h4
      simpa [commutatorElement_def] using this
    have h5 : ⁅a, x⁆ ∈ A := by
      have h6 : x * a⁻¹ * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hxA _).1 (A.inv_mem haA)
      rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc x]
      exact A.mul_mem haA h6
    exact hax ⟨h5, h3⟩
  have hidx : (Q.subgroupOf G₀).index ≤ Nat.card (alternatingGroup (Fin n)) := by
    have hsup : A.subgroupOf G₀ ⊔ Q.subgroupOf G₀ = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hAG hQG, Subgroup.subgroupOf_self]
    have h1 : (Q.subgroupOf G₀).index = Q.relIndex A := by
      rw [← Subgroup.relIndex_top_right, ← hsup, Subgroup.relIndex_sup_right,
        Subgroup.relIndex_subgroupOf hAG]
    have h2 : Q.relIndex A = (zStar A).relIndex A := by
      rw [← Subgroup.inf_relIndex_right Q A, inf_comm]
      rfl
    obtain ⟨-, -, ⟨e⟩⟩ := hA.2
    rw [h1, h2, ← Nat.card_congr e.toEquiv]
    exact relIndex_zStar_le A
  have hJle : ∀ J, Sec6KComp X n H J → J ≤ Q := by
    intro J hJ
    by_contra hJQ
    have hJKx : J ≤ Sec6K X n H := le_sSup hJ
    have hJK : J ≤ Sec6K X n N := hJKx.trans hKx
    have hJG : J ≤ G₀ := hJK.trans hKG
    have hJpc := isPCompIn_of_sec6KComp hJ
    have hJq : IsTwoGenQuasi ↥J :=
      (isTwoGenQuasi_subgroupOf_iff hJpc.1).1 (isPComponent_two_iff.1 hJpc.2).2
    have hJn : J ≤ normalizer ((J ⊓ Q : Subgroup X) : Set X) := fun j hj =>
      mem_normalizer_inf (Subgroup.le_normalizer hj) (mem_normalizer_QOf (hKnA (hJK hj)))
    have h1 := card_quot_center_le_relIndex hJq inf_le_left hJn
      (fun h => hJQ (h.trans inf_le_right))
    have h2 := card_alt_le_of_sec6KComp hcf hJ
    have hJ'C : J.subgroupOf G₀ ≤ C₀ := by
      intro j hj
      show π₀ j ∈ centralizer _
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have hjx : (j : X) * x = x * j := Subgroup.mem_centralizer_singleton_iff.1 (hH (hJpc.1 hj))
      simp only [Subgroup.coe_mul]
      exact hjx
    have e1 : (J ⊓ Q).relIndex J = (Q.subgroupOf G₀).relIndex (J.subgroupOf G₀) := by
      rw [inf_comm, Subgroup.inf_relIndex_right, Subgroup.relIndex_subgroupOf hJG]
    have h3 : (Q.subgroupOf G₀).relIndex (J.subgroupOf G₀) ≤ (Q.subgroupOf G₀).relIndex C₀ :=
      Subgroup.relIndex_le_of_le_right hJ'C
        (by rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
    have h4 : (Q.subgroupOf G₀).relIndex C₀ * C₀.index = (Q.subgroupOf G₀).index :=
      Subgroup.relIndex_mul_index hQC
    have h5 : 1 < C₀.index := Subgroup.one_lt_index_of_ne_top hC₀
    have hpos : 0 < Nat.card (alternatingGroup (Fin n)) := Nat.card_pos
    have h6 : (Q.subgroupOf G₀).relIndex C₀ * 2 ≤ (Q.subgroupOf G₀).index := by
      rw [← h4]
      exact Nat.mul_le_mul_left _ h5
    omega
  have hKQ : Sec6K X n H ≤ Q := sSup_le fun J hJ => hJle J hJ
  exact hxQ (hKQ hxK)

theorem mem_sec6R_of_mem_QOf (hcf : McLLyCenterFree) {n : ℕ} {N : Subgroup X} {x : X}
    (hxK : x ∈ Sec6K X n N) (hxQ : ∀ A, Sec5Comp X n N A → x ∈ QOf A) : x ∈ Sec6R X n N := by
  set K0N := K0 X n N with hK0N
  have hMn : Sec6M X n N ≤ normalizer (K0N : Set X) := fun c hc =>
    mem_normalizer_of_map_conj_eq (map_conj_K0 n (Subgroup.le_normalizer (sec6M_le n N hc)))
  rw [sec6K_eq, sup_comm] at hxK
  obtain ⟨m, hm, a, ha, rfl⟩ := exists_mul_of_mem_sup hMn hxK
  have hMQ : ∀ A, Sec5Comp X n N A → Sec6M X n N ≤ QOf A := fun A hA =>
    sSup_le fun M hM => le_QOf_of_ne (isPCompIn_of_sec6KComp (Or.inl hA)) hM.1.1
      (ne_of_sec5Comp_of_sec6MComp hcf hA hM)
  have haQ : ∀ A, Sec5Comp X n N A → a ∈ QOf A := fun A hA => by
    have h1 := (QOf A).mul_mem ((QOf A).inv_mem (hMQ A hA hm)) (hxQ A hA)
    rwa [inv_mul_cancel_left] at h1
  have hOK : ∀ A, Sec5Comp X n N A → oddCoreOf A ≤ oddCoreOf K0N := fun A hA => by
    have hApc : IsPCompIn 2 N A := isPCompIn_of_sec6KComp (Or.inl hA)
    have hAK : A ≤ K0N := le_sSup hA
    have h1 := isPComponent_subgroupOf_mono hAK (K0_le n N) hApc.2
    exact pPrimeCoreOf_le_oddCoreOf hAK (isPComponent_two_iff.1 h1).1
  have hcomm : ∀ k ∈ K0N, ⁅k, a⁆ ∈ oddCoreOf K0N := by
    intro k hk
    have hk' : k ∈ ⨆ L : ↥{L : Subgroup X | Sec5Comp X n N L}, (L : Subgroup X) := by
      rw [← sSup_eq_iSup', ← K0_eq_sSup_sec5Comp]
      exact hk
    refine (Subgroup.iSup_induction (fun L : ↥{L : Subgroup X | Sec5Comp X n N L} =>
      (L : Subgroup X)) (C := fun k => k ∈ K0N ∧ ⁅k, a⁆ ∈ oddCoreOf K0N) hk' ?_ ?_ ?_).2
    · rintro ⟨L, hL⟩ y hy
      exact ⟨(le_sSup hL : L ≤ K0N) hy, hOK L hL ((mem_QOf_iff.1 (haQ L hL)).2 y hy)⟩
    · refine ⟨one_mem _, ?_⟩
      rw [commutatorElement_def, one_mul, inv_one, mul_one, mul_inv_cancel]
      exact one_mem _
    · rintro y z ⟨hy, hya⟩ ⟨hz, hza⟩
      refine ⟨K0N.mul_mem hy hz, ?_⟩
      have e : ⁅y * z, a⁆ = y * ⁅z, a⁆ * y⁻¹ * ⁅y, a⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (oddCoreOf K0N).mul_mem
        ((Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf K0N hy) _).1 hza) hya
  have hazs : a ∈ zStar K0N :=
    ⟨ha, Subgroup.le_normalizer ha, le_normalizer_oddCoreOf K0N ha, hcomm⟩
  exact Subgroup.mul_mem _ ((le_sup_right : Sec6M X n N ≤ Sec6R X n N) hm)
    ((le_sup_left : zStar K0N ≤ Sec6R X n N) hazs)

end StepTwoD

end Sec6Fus

open Sec6Fus

section Fields

variable {X : Type} [Group X] [Finite X] {n : ℕ} {t : X}

theorem sec6M_cen_le_of_le (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n) {N : Subgroup X}
    (hN : N ≠ ⊤) (hCt : cen t ≤ N) : Sec6M X n (cen t) ≤ Sec6M X n N := by
  have htN : t ∈ N := hCt (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have h := (hK.b N hN t htN hS.choice.inv).2
  rwa [inf_eq_right.2 hCt] at h

theorem exists_involution_sec6M (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n) {N : Subgroup X}
    (hN : N ≠ ⊤) (hCt : cen t ≤ N) : ∃ v ∈ Sec6M X n N, orderOf v = 2 := by
  obtain ⟨M, hM⟩ := hS.choice.hasM
  have hpc : IsPCompIn 2 (cen t) M := hM.1.1
  have hq : IsTwoGenQuasi ↥M :=
    (isTwoGenQuasi_subgroupOf_iff hpc.1).1 (isPComponent_two_iff.1 hpc.2).2
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial ↥M := by
    by_contra hnot
    rw [not_nontrivial_iff_subsingleton] at hnot
    obtain ⟨a, b, hab⟩ := hq.2.2.2
    exact hab (Subsingleton.elim (a * b) (b * a))
  have hdvd : 2 ∣ Nat.card ↥M := by
    by_contra hnd
    have hcop : Nat.Coprime 2 (Nat.card ↥M) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hnd
    have h1 := ComponentClassification.CatalogueBPrimeJoin.primeResidual_eq_bot_of_coprime_card
      (G := ↥M) 2 hcop
    rw [hq.1] at h1
    exact top_ne_bot h1
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hMle : M ≤ Sec6M X n (cen t) := le_sSup hM
  exact ⟨v, sec6M_cen_le_of_le hS hK hN hCt (hMle v.2), by rw [Subgroup.orderOf_coe]; exact hv⟩

theorem sec6Fusion_inv (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n) {N : Subgroup X}
    (hN : N ≠ ⊤) (hCt : cen t ≤ N) : ∃ y ∈ Sec6Y X n N, orderOf y = 2 := by
  obtain ⟨v, hv, hv2⟩ := exists_involution_sec6M hS hK hN hCt
  exact ⟨v, (le_sup_left : Sec6R X n N ≤ Sec6Y X n N)
    ((le_sup_right : Sec6M X n N ≤ Sec6R X n N) hv), hv2⟩

theorem exists_conj_mem_sec6R {N : Subgroup X} {y : X} (hy : y ∈ Sec6Y X n N)
    (hy2 : orderOf y = 2) :
    ∃ h ∈ Sec6Y X n N, h * y * h⁻¹ ∈ Sec6R X n N ∧ orderOf (h * y * h⁻¹) = 2 := by
  obtain ⟨h, hh, hr⟩ := exists_conj_mem_of_sup_odd
    (fun c hc => mem_normalizer_oddCoreOf_sec6K n (sec6R_le n N hc))
    (odd_card_oddCoreOf _) hy (sq_eq_one_of_orderOf hy2)
  exact ⟨h, hh, hr, by rw [orderOf_conj]; exact hy2⟩

theorem sec6Fusion_cen {N : Subgroup X}
    (hI : ∀ x ∈ Sec6R X n N, orderOf x = 2 → cen x ≤ N) :
    ∀ y ∈ Sec6Y X n N, orderOf y = 2 → centralizer ({y} : Set X) ≤ N := by
  intro y hy hy2 c hc
  obtain ⟨h, hh, hr, hr2⟩ := exists_conj_mem_sec6R hy hy2
  have hhN : h ∈ N := sec6Y_le n N hh
  have hcy : c * y = y * c := Subgroup.mem_centralizer_singleton_iff.1 hc
  have hc' : h * c * h⁻¹ ∈ cen (h * y * h⁻¹) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc h * c * h⁻¹ * (h * y * h⁻¹) = h * (c * y) * h⁻¹ := by group
      _ = h * (y * c) * h⁻¹ := by rw [hcy]
      _ = h * y * h⁻¹ * (h * c * h⁻¹) := by group
  have hcN := hI _ hr hr2 hc'
  have := N.mul_mem (N.mul_mem (N.inv_mem hhN) hcN) hhN
  rwa [show h⁻¹ * (h * c * h⁻¹) * h = c by group] at this

theorem sec6Fusion_conj {N : Subgroup X}
    (hI : ∀ x ∈ Sec6R X n N, orderOf x = 2 → cen x ≤ N) :
    ∀ x ∈ sec6D (Sec6Y X n N), ∀ z ∈ sec6D (Sec6Y X n N), Commute x z →
      ∃ g : X, g * x * g⁻¹ ∈ N ∧ g * z * g⁻¹ ∈ N := by
  rintro x ⟨g, y, hy, hy2, rfl⟩ z - hxz
  refine ⟨g⁻¹, ?_, ?_⟩
  · rw [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group]
    exact sec6Y_le n N hy
  · apply sec6Fusion_cen hI y hy hy2
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hxz.eq
    calc g⁻¹ * z * g⁻¹⁻¹ * y = g⁻¹ * (z * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * z) * g := by rw [h]
      _ = y * (g⁻¹ * z * g⁻¹⁻¹) := by group

theorem not_isSolvable_cen_of_mem_sec6R (hcf : McLLyCenterFree) (hS : Sec6Setting X n t)
    (hK : Sec6Lemma51 X n) {N : Subgroup X} (hN : N ≠ ⊤) (hCt : cen t ≤ N) {r : X}
    (hr : r ∈ Sec6R X n N) (hr2 : orderOf r = 2) : ¬ Group.IsSolvable ↥(cen r) := by
  have hr2' : r ^ 2 = 1 := sq_eq_one_of_orderOf hr2
  by_cases hA : ∃ A, Sec5Comp X n N A
  · obtain ⟨A, hA⟩ := hA
    have hApc : IsPCompIn 2 N A := isPCompIn_of_sec6KComp (Or.inl hA)
    have hAK : A ≤ K0 X n N := le_sSup hA
    have hKnA : K0 X n N ≤ normalizer (A : Set X) :=
      sSup_le_normalizer hApc fun J hJ => isPCompIn_of_sec6KComp (Or.inl hJ)
    have hle : A ⊓ oddCoreOf (K0 X n N) ≤ oddCoreOf A := by
      refine le_oddCoreOf_of_normalized inf_le_left (fun a ha => ?_) ?_
      · exact mem_normalizer_inf (Subgroup.le_normalizer ha)
          (le_normalizer_oddCoreOf _ (hAK ha))
      · exact Odd.of_dvd_nat (odd_card_oddCoreOf _) (Subgroup.card_dvd_of_le inf_le_right)
    have hRQ : Sec6R X n N ≤ QOf A := by
      refine sup_le ?_ (sSup_le fun M hM => le_QOf_of_ne hApc hM.1.1
        (ne_of_sec5Comp_of_sec6MComp hcf hA hM))
      rintro z ⟨hzK, -, -, hz⟩
      have hzA : z ∈ normalizer (A : Set X) := hKnA hzK
      refine mem_QOf_iff.2 ⟨hzA, fun a ha => hle ⟨?_, hz a (hAK ha)⟩⟩
      have h1 : z * a⁻¹ * z⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hzA _).1 (A.inv_mem ha)
      rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc z]
      exact A.mul_mem ha h1
    exact fun hs => not_isSolvable_inf_cen_of_mem_QOf hApc hr2' (hRQ hr)
      (isSolvable_of_le inf_le_right hs)
  · push Not at hA
    have hK0 : K0 X n N = ⊥ := by
      rw [K0_eq_sSup_sec5Comp]
      exact sSup_eq_bot.2 fun A hA' => absurd hA' (hA A)
    have hrM : r ∈ Sec6M X n N := by
      refine (sup_le (fun z hz => ?_) le_rfl : Sec6R X n N ≤ Sec6M X n N) hr
      have h1 := zStar_le _ hz
      rw [hK0, Subgroup.mem_bot] at h1
      rw [h1]
      exact one_mem _
    obtain ⟨v, hv, hv2⟩ := exists_involution_sec6M hS hK hN hCt
    have hF : ∃ F, Sec6MComp X n N F := by
      by_contra hno
      push Not at hno
      have h0 : Sec6M X n N = ⊥ := sSup_eq_bot.2 fun F hF => absurd hF (hno F)
      rw [h0, Subgroup.mem_bot] at hv
      rw [hv, orderOf_one] at hv2
      exact absurd hv2 (by decide)
    obtain ⟨F, hF⟩ := hF
    have hMF : Sec6M X n N ≤ QOf F ⊔ F := sSup_le fun M hM => by
      by_cases hFM : F = M
      · rw [← hFM]
        exact le_sup_right
      · exact (le_QOf_of_ne hF.1.1 hM.1.1 hFM).trans le_sup_left
    exact fun hs => not_isSolvable_inf_cen_of_isMLIntrIn hcf hF.1 hr2' (hMF hrM)
      (isSolvable_of_le inf_le_right hs)

theorem sec6Fusion_ns (hcf : McLLyCenterFree) (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n)
    {N : Subgroup X} (hN : N ≠ ⊤) (hCt : cen t ≤ N) :
    ∀ y ∈ Sec6Y X n N, orderOf y = 2 → ¬ Group.IsSolvable ↥(centralizer ({y} : Set X)) := by
  intro y hy hy2
  obtain ⟨h, -, hr, hr2⟩ := exists_conj_mem_sec6R hy hy2
  have h2 := not_isSolvable_cen_conj h⁻¹ (not_isSolvable_cen_of_mem_sec6R hcf hS hK hN hCt hr hr2)
  rwa [show h⁻¹ * (h * y * h⁻¹) * h⁻¹⁻¹ = y by group] at h2

@[expose] def Sec6FusMemK (X : Type) [Group X] (n : ℕ) (N : Subgroup X) : Prop :=
  ∀ x ∈ N, ∀ g y : X, y ∈ Sec6R X n N → orderOf y = 2 → x = g * y * g⁻¹ →
    x ∈ Sec6K X n (N ⊓ cen x)

@[expose] def Sec6FusIII (X : Type) [Group X] (n : ℕ) (N : Subgroup X) : Prop :=
  ∀ y ∈ Sec6R X n N, orderOf y = 2 → y ∈ Sec6K X n (cen y)

@[expose] def Sec6FusStep2 (X : Type) [Group X] (n : ℕ) (N : Subgroup X) : Prop :=
  ∀ x ∈ N, ∀ g y : X, y ∈ Sec6R X n N → orderOf y = 2 → x = g * y * g⁻¹ →
    Sec6K X n (cen x) ≤ N

theorem mem_sec6K_cen_conj {y : X} (hy : y ∈ Sec6K X n (cen y)) (g : X) :
    g * y * g⁻¹ ∈ Sec6K X n (cen (g * y * g⁻¹)) := by
  have h1 := Sec6K_map n (MulAut.conj g) (cen y)
  rw [cen_map] at h1
  have h2 : (MulAut.conj g) y ∈ (Sec6K X n (cen y)).map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hy
  rw [h1] at h2
  simpa only [MulAut.conj_apply] using h2

theorem sec6K_cen_le_sec6K_inf {N : Subgroup X} {x : X} (hle : Sec6K X n (cen x) ≤ N) :
    Sec6K X n (cen x) ≤ Sec6K X n (N ⊓ cen x) := by
  refine sSup_le fun J hJ => le_sSup ?_
  have hJx : J ≤ Sec6K X n (cen x) := le_sSup hJ
  have hJN : J ≤ N := hJx.trans hle
  have hpc : ∀ {L : Subgroup X}, IsPCompIn 2 (cen x) L → L ≤ N → IsPCompIn 2 (N ⊓ cen x) L :=
    fun h hLN => ⟨le_inf hLN h.1, isPComponent_subgroupOf_mono (le_inf hLN h.1) inf_le_right h.2⟩
  rcases hJ with ⟨⟨u, hu1, hu2, hu3, hu4, hu5⟩, hJ2⟩ | ⟨⟨hJ1, hJ2, hJ3⟩, hJ4⟩
  · exact Or.inl ⟨⟨u, hu1, hu2, hpc hu3 hJN, hu4, hu5⟩, hJ2⟩
  · exact Or.inr ⟨⟨hpc hJ1 hJN, hJ2, hJ3⟩, hJ4⟩

theorem sec6FusMemK_of_step2 {N : Subgroup X} (hIII : Sec6FusIII X n N)
    (h2 : Sec6FusStep2 X n N) : Sec6FusMemK X n N := by
  rintro x hxN g y hy hy2 rfl
  exact sec6K_cen_le_sec6K_inf (h2 _ hxN g y hy hy2 rfl) (mem_sec6K_cen_conj (hIII y hy hy2) g)

theorem sec6Fusion_fus
    (hK : Sec6Lemma51 X n) {N : Subgroup X} (hN : N ≠ ⊤) (hM : Sec6FusMemK X n N) :
    ∀ x ∈ sec6D (Sec6Y X n N), x ∈ N → x ∈ Sec6Y X n N := by
  rintro x ⟨g, y, hy, hy2, rfl⟩ hxN
  obtain ⟨h, -, hr, hr2⟩ := exists_conj_mem_sec6R hy hy2
  have hx : g * y * g⁻¹ = (g * h⁻¹) * (h * y * h⁻¹) * (g * h⁻¹)⁻¹ := by group
  rw [hx] at hxN ⊢
  have hx2 : orderOf ((g * h⁻¹) * (h * y * h⁻¹) * (g * h⁻¹)⁻¹) = 2 := by
    rw [orderOf_conj]
    exact hr2
  have hxK := hM _ hxN (g * h⁻¹) _ hr hr2 rfl
  have hKx := (hK.b N hN _ hxN hx2).1
  exact (le_sup_left : Sec6R X n N ≤ Sec6Y X n N)
    (mem_sec6R_of_mem_QOf mcLLyCenterFree (hKx hxK)
      fun A hA => mem_QOf_of_mem_sec6K mcLLyCenterFree inf_le_right hxK hKx hA)

end Fields

theorem sec6Thm64Fusion_of_ctrl
    {X : Type} [Group X] [Finite X] {n : ℕ} {t : X}
    (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n) (h61 : Sec6L61 X n t)
    (hC : Sec6CtrlAt X n t) (N : Subgroup X) (hN : N ≠ ⊤) (hCt : cen t ≤ N)
    (hII : Sec6CtrlNAt X n t N)
    (hI : ∀ x ∈ Sec6R X n N, orderOf x = 2 → cen x ≤ N)
    (hM : Sec6FusMemK X n N) :
    Sec6Fusion X N (Sec6Y X n N) where
  ne_top := hN
  le := sec6Y_le n N
  conj := sec6Fusion_conj hI
  fus := sec6Fusion_fus hK hN hM
  cen := sec6Fusion_cen hI
  inv := sec6Fusion_inv hS hK hN hCt
  ns := sec6Fusion_ns mcLLyCenterFree hS hK hN hCt

end CFSG.OddStandard.Solomon75
