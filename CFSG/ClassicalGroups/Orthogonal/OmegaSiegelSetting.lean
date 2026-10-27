module

public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelRoot
public import CFSG.ClassicalGroups.Orthogonal.SiegelI4FamilyDichotomy
public import CFSG.RankThree.GF2n.Smith81.OrthRootInvol
public import CFSG.RankThree.GF2n.Smith81.Orth28Omega
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.SpecialLinear.TransvectionPencils
public import CFSG.HardMathSupport.Kantor79.LongRootElementClass
public import CFSG.HardMathSupport.Kantor79.OverlappingLongRoot

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open CFSG.HardMathSupport.Kantor79 CFSG.ClassicalGroups.Orthogonal.SiegelRT1
open CFSG.ClassicalGroups.Orthogonal.SiegelSL CFSG.RankThree.GF2n.Smith81 QuadraticMap Module
open scoped commutatorElement

variable {K' : Type*} [Field K'] [CharP K' 2] {N : Type*} [AddCommGroup N] [Module K' N]
  {QN : QuadraticForm K' N} {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V]
  [Module K V] {Qf : QuadraticForm K V}

structure OmegaSetting (QN : QuadraticForm K' N) (Qf : QuadraticForm K V)
    (ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)) : Prop where
  card : Nat.card K' = Nat.card K
  ndN : (polarBilin QN).Nondegenerate
  nd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0
  inj : Function.Injective ρ
  iso : ∀ g v, Qf (ρ g v) = Qf v
  siegel : ∀ s : ↥(elementaryGroup QN), IsOrthA2 QN (s : N ≃ₗ[K'] N) →
    IsLongRootElement Qf (ρ s)

@[expose] noncomputable def rhoE (ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)) (u w : N) :
    V ≃ₗ[K] V :=
  ρ ⟨eichler QN u w, eichler_mem_elementaryGroup QN u w⟩

variable {ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)}

omit [CharP K' 2] [CharP K 2] in
theorem rhoE_mul {u v w : N} (hv : polar QN u v = 0) (hw : polar QN u w = 0) :
    rhoE ρ u v * rhoE ρ u w = rhoE ρ u (v + w) := by
  unfold rhoE
  rw [← map_mul]
  exact congrArg ρ (Subtype.ext (eichler_mul hv hw))

omit [CharP K 2] in
theorem rhoE_comm {a b : N} (ha : QN a = 0) (hb : QN b = 0) (hab : polar QN a b = 0) :
    rhoE ρ a b = rhoE ρ b a := by
  unfold rhoE
  exact congrArg ρ (Subtype.ext (eichler_comm_of_singular ha hb hab))

omit [CharP K' 2] [CharP K 2] in
theorem rhoE_smul_left (c : K') (u w : N) : rhoE ρ (c • u) w = rhoE ρ u (c • w) := by
  unfold rhoE
  exact congrArg ρ (Subtype.ext (eichler_smul_left c u w))

omit [CharP K' 2] [CharP K 2] in
theorem rhoE_zero_right (u : N) : rhoE ρ u 0 = 1 := by
  unfold rhoE
  rw [← map_one ρ]
  exact congrArg ρ (Subtype.ext (eichler_zero_right QN u))

theorem IsLongRootElement.isOrthA2 [FiniteDimensional K' N] (hnd : (polarBilin QN).Nondegenerate)
    {s : N ≃ₗ[K'] N} (hs : IsLongRootElement QN s) : IsOrthA2 QN s := by
  have hnd' : ∀ x : N, (∀ y, polar QN x y = 0) → x = 0 := fun x hx => hnd.1 x fun y => hx y
  exact ⟨hs.mem_orthogonalGroup, hs.mul_self, hs.finrank_movedSpace hnd',
    fun x hx => hs.qf_eq_zero_of_mem_movedSpace hx⟩

theorem omegaSetting_of_exists [Finite K'] [FiniteDimensional K' N] {m : ℕ}
    (hdim : finrank K' N = 2 * m) (hm : 3 ≤ m) (hcard : Nat.card K' = Nat.card K)
    (hndN : (polarBilin QN).Nondegenerate) (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    (hinj : Function.Injective ρ) (hiso : ∀ g v, Qf (ρ g v) = Qf v)
    (h₀ : ∃ t₀ : ↥(elementaryGroup QN), IsOrthA2 QN (t₀ : N ≃ₗ[K'] N) ∧
      IsLongRootElement Qf (ρ t₀)) :
    OmegaSetting QN Qf ρ := by
  obtain ⟨t₀, ht₀, hρt₀⟩ := h₀
  refine ⟨hcard, hndN, hnd, hinj, hiso, fun s hs => ?_⟩
  obtain ⟨g, hg, hgts⟩ := isOrthA2_conj_omega hndN hdim (by omega) hs ht₀
  have hgE : g ∈ elementaryGroup QN :=
    omegaGroup_le_elementaryGroup_of_four_le hndN (by omega) hg
  have hs' : s = ⟨g, hgE⟩ * t₀ * ⟨g, hgE⟩⁻¹ := Subtype.ext hgts.symm
  have hρg : ρ ⟨g, hgE⟩ ∈ TauCeti.QuadraticMap.orthogonalGroup Qf :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hiso _)
  rw [hs', map_mul, map_mul, map_inv]
  exact IsLongRootElement.conj hρg hρt₀

omit [CharP K 2] in
theorem OmegaSetting.isLongRootElement_rhoE [FiniteDimensional K' N]
    (hs : OmegaSetting QN Qf ρ) {a b : N} (ha : QN a = 0) (hb : QN b = 0)
    (hab : polar QN a b = 0) (hli : LinearIndependent K' ![a, b]) :
    IsLongRootElement Qf (rhoE ρ a b) :=
  hs.siegel _ (isOrthA2_eichler hs.ndN ha hb hab hli).1

omit [CharP K 2] in
private theorem exists_polar_eq_of_linearIndependent
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {n : ℕ} {t : Fin n → V}
    (ht : LinearIndependent K t) (c : Fin n → K) : ∃ v : V, ∀ i, polar Qf (t i) v = c i := by
  let φ : V →ₗ[K] (Fin n → K) := LinearMap.pi fun i => polarBilin Qf (t i)
  have hφ : Function.Surjective φ := by
    rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
    intro ℓ hℓ
    set a : Fin n → K := fun i => ℓ fun j => if i = j then 1 else 0
    have hsum : ∀ v, polar Qf (∑ i, a i • t i) v = 0 := by
      intro v
      have h1 := LinearMap.congr_fun hℓ v
      rw [LinearMap.dualMap_apply, LinearMap.zero_apply, LinearMap.pi_apply_eq_sum_univ] at h1
      rw [← polarBilin_apply_apply, map_sum, LinearMap.sum_apply]
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [φ, a, mul_comm]
    have ha : a = 0 := by
      funext i
      exact Fintype.linearIndependent_iff.mp ht a (hnd _ hsum) i
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : (ℓ fun j => if i = j then (1 : K) else 0) = a i := rfl
    rw [this, ha, Pi.zero_apply, smul_zero]
  obtain ⟨v, hv⟩ := hφ c
  exact ⟨v, fun i => by simpa [φ] using congrFun hv i⟩

private theorem movedSpace_eq_span_pair (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {x : V ≃ₗ[K] V} (hx : IsLongRootElement Qf x) {p q : V} (hli : LinearIndependent K ![p, q])
    (hxf : ∀ v, x v = v + polar Qf v q • p + polar Qf v p • q) :
    movedSpace x = Submodule.span K ({p, q} : Set V) := by
  have hspan : finrank K (Submodule.span K ({p, q} : Set V)) = 2 := by
    have h := finrank_span_eq_card hli
    rw [show Set.range ![p, q] = ({p, q} : Set V) by ext x; simp [eq_comm, or_comm]] at h
    simpa using h
  have hle : movedSpace x ≤ Submodule.span K ({p, q} : Set V) := by
    rintro _ ⟨v, rfl⟩
    change x v - v ∈ _
    rw [hxf v, add_assoc, add_sub_cancel_left]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have : FiniteDimensional K (Submodule.span K ({p, q} : Set V)) :=
    FiniteDimensional.span_of_finite K (Set.toFinite _)
  exact Submodule.eq_of_le_of_finrank_eq hle ((hx.finrank_movedSpace hnd).trans hspan.symm)

omit [CharP K 2] in
private theorem mul_apply_sub_eq_of_disjoint {x y : V ≃ₗ[K] V} (hxy : x * y = y * x)
    (h0 : movedSpace x ⊓ movedSpace y = ⊥) (v : V) :
    (x * y) v - v = (x v - v) + (y v - v) := by
  have hc : x (y v) = y (x v) := by
    simpa only [LinearEquiv.mul_apply] using DFunLike.congr_fun hxy v
  have h1 : x (y v - v) - (y v - v) ∈ movedSpace x ⊓ movedSpace y := by
    refine ⟨sub_mem_movedSpace x _, ?_⟩
    have : x (y v - v) - (y v - v) = (y (x v) - x v) - (y v - v) := by
      rw [map_sub, hc]
    rw [this]
    exact Submodule.sub_mem _ (sub_mem_movedSpace y _) (sub_mem_movedSpace y _)
  rw [h0, Submodule.mem_bot, sub_eq_zero] at h1
  rw [LinearEquiv.mul_apply]
  calc x (y v) - v = x ((y v - v) + v) - v := by rw [sub_add_cancel]
    _ = (x v - v) + (y v - v) := by rw [map_add, h1]; abel

omit [CharP K 2] in
private theorem linearIndependent_four_of_disjoint {p q p' q' : V}
    (hli : LinearIndependent K ![p, q]) (hli' : LinearIndependent K ![p', q'])
    (h0 : Submodule.span K ({p, q} : Set V) ⊓ Submodule.span K ({p', q'} : Set V) = ⊥) :
    LinearIndependent K ![p, q, p', q'] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three] at hc
  have hc' : (c 0 • p + c 1 • q) + (c 2 • p' + c 3 • q') = 0 := by
    rw [← hc]
    abel
  have hu : c 0 • p + c 1 • q ∈
      Submodule.span K ({p, q} : Set V) ⊓ Submodule.span K ({p', q'} : Set V) := by
    refine ⟨?_, ?_⟩
    · exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · rw [eq_neg_of_add_eq_zero_left hc']
      exact Submodule.neg_mem _ (Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
  rw [h0, Submodule.mem_bot] at hu
  obtain ⟨e0, e1⟩ := LinearIndependent.pair_iff.mp hli _ _ hu
  rw [hu, zero_add] at hc'
  obtain ⟨e2, e3⟩ := LinearIndependent.pair_iff.mp hli' _ _ hc'
  intro i
  fin_cases i <;> assumption

private theorem movedSpace_inf_ne_bot_of_commute' (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {x y : V ≃ₗ[K] V} (hx : IsLongRootElement Qf x) (hy : IsLongRootElement Qf y)
    (hxy : x * y = y * x) (hz : IsLongRootElement Qf (x * y)) :
    movedSpace x ⊓ movedSpace y ≠ ⊥ := by
  intro h0
  obtain ⟨p, q, -, -, -, -, -, hli, hxf⟩ := id hx
  obtain ⟨p', q', -, -, -, -, -, hli', hyf⟩ := id hy
  have ht := linearIndependent_four_of_disjoint hli hli'
    (by rw [← movedSpace_eq_span_pair hnd hx hli hxf, ← movedSpace_eq_span_pair hnd hy hli' hyf]
        exact h0)
  have hcalc : ∀ v, (x * y) v - v = polar Qf q v • p + polar Qf p v • q +
      (polar Qf q' v • p' + polar Qf p' v • q') := by
    intro v
    rw [mul_apply_sub_eq_of_disjoint hxy h0, hxf v, hyf v, polar_comm Qf v q, polar_comm Qf v p,
      polar_comm Qf v q', polar_comm Qf v p']
    abel
  have key : ∀ c : Fin 4 → K,
      c 1 • p + c 0 • q + (c 3 • p' + c 2 • q') ∈ movedSpace (x * y) := by
    intro c
    obtain ⟨v, hv⟩ := exists_polar_eq_of_linearIndependent hnd ht c
    have e0 : polar Qf p v = c 0 := by simpa using hv 0
    have e1 : polar Qf q v = c 1 := by simpa using hv 1
    have e2 : polar Qf p' v = c 2 := by simpa using hv 2
    have e3 : polar Qf q' v = c 3 := by simpa using hv 3
    refine mem_movedSpace_iff.mpr ⟨v, ?_⟩
    rw [hcalc, e0, e1, e2, e3]
  have hT : ∀ i : Fin 4, (![p, q, p', q'] : Fin 4 → V) i ∈ movedSpace (x * y) := by
    intro i
    fin_cases i
    · simpa using key ![0, 1, 0, 0]
    · simpa using key ![1, 0, 0, 0]
    · simpa using key ![0, 0, 0, 1]
    · simpa using key ![0, 0, 1, 0]
  have : Module.Finite K (movedSpace (x * y)) :=
    Module.finite_of_finrank_pos (by rw [hz.finrank_movedSpace hnd]; norm_num)
  have hind : LinearIndependent K (fun i => (⟨_, hT i⟩ : movedSpace (x * y))) :=
    LinearIndependent.of_comp (movedSpace (x * y)).subtype ht
  have hcard := hind.fintype_card_le_finrank
  rw [hz.finrank_movedSpace hnd, Fintype.card_fin] at hcard
  omega

theorem OmegaSetting.movedSpace_rhoE_inf_ne_bot [FiniteDimensional K' N]
    (hs : OmegaSetting QN Qf ρ) {a b b' : N} (ha : QN a = 0) (hb : QN b = 0) (hb' : QN b' = 0)
    (hab : polar QN a b = 0) (hab' : polar QN a b' = 0) (hbb' : polar QN b b' = 0)
    (hli : LinearIndependent K' ![a, b]) (hli' : LinearIndependent K' ![a, b'])
    (hli'' : LinearIndependent K' ![a, b + b']) :
    movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a b') ≠ ⊥ := by
  have hQ : QN (b + b') = 0 := by
    rw [QuadraticMap.map_add QN b b', hb, hb', hbb', add_zero, add_zero]
  have hB : polar QN a (b + b') = 0 := by rw [polar_add_right, hab, hab', add_zero]
  have hxy : rhoE ρ a b * rhoE ρ a b' = rhoE ρ a (b + b') := rhoE_mul hab hab'
  have hyx : rhoE ρ a b' * rhoE ρ a b = rhoE ρ a (b + b') := by
    rw [rhoE_mul hab' hab, add_comm]
  refine movedSpace_inf_ne_bot_of_commute' hs.nd (hs.isLongRootElement_rhoE ha hb hab hli)
    (hs.isLongRootElement_rhoE ha hb' hab' hli') (hxy.trans hyx.symm) ?_
  rw [hxy]
  exact hs.isLongRootElement_rhoE ha hQ hB hli''

private theorem commute_of_inf_ne_bot' [FiniteDimensional K V]
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {s s' : V ≃ₗ[K] V}
    (hs : IsLongRootElement Qf s) (hs' : IsLongRootElement Qf s')
    (h : movedSpace s ⊓ movedSpace s' ≠ ⊥) : s * s' = s' * s := by
  have hQ := nondegenerate_polarBilin hnd
  obtain ⟨a, b, ha, hb, hab, hli, hmem, hne⟩ :=
    (isLongRootElement_iff_exists_mem_longRootGroup hQ).mp hs
  obtain ⟨a', b', ha', hb', hab', hli', hmem', hne'⟩ :=
    (isLongRootElement_iff_exists_mem_longRootGroup hQ).mp hs'
  have h1 := (mem_longRootGroup_isLongRootElement hnd hli hmem hne).2
  have h2 := (mem_longRootGroup_isLongRootElement hnd hli' hmem' hne').2
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.mp hu
  refine longRootGroup_comm_of_common hQ ha hb hab ha' hb' hab'
    (hs.qf_eq_zero_of_mem_movedSpace hu1) hu0 ?_ ?_ hmem hmem'
  · rwa [h1] at hu1
  · rwa [h2] at hu2

theorem OmegaSetting.movedSpace_rhoE_inf_eq_bot [FiniteDimensional K' N] [FiniteDimensional K V]
    (hs : OmegaSetting QN Qf ρ) {a b c d : N} (ha : QN a = 0) (hb : QN b = 0) (hc : QN c = 0)
    (hd : QN d = 0) (hab : polar QN a b = 0) (hcd : polar QN c d = 0) (hac : polar QN a c = 0)
    (had : polar QN a d = 0) (hbd : polar QN b d = 0) (hbc : polar QN b c ≠ 0)
    (hlab : LinearIndependent K' ![a, b]) (hlcd : LinearIndependent K' ![c, d])
    (hlad : LinearIndependent K' ![a, d]) :
    movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ c d) = ⊥ := by
  by_contra hne
  have hcomm := commute_of_inf_ne_bot' hs.nd (hs.isLongRootElement_rhoE ha hb hab hlab)
    (hs.isLongRootElement_rhoE hc hd hcd hlcd) hne
  unfold rhoE at hcomm
  rw [← map_mul, ← map_mul] at hcomm
  have hcomm' : eichler QN a b * eichler QN c d = eichler QN c d * eichler QN a b :=
    congrArg Subtype.val (hs.inj hcomm)
  have h1 := commutatorElement_eq_one_iff_mul_comm.mpr hcomm'
  rw [commutatorElement_eichler ha hb hc hd hab hcd hac had hbd] at h1
  have hβ : polar QN b c ≠ 0 := hbc
  have hli : LinearIndependent K' ![a, polar QN b c • d] := by
    rw [LinearIndependent.pair_iff] at hlad ⊢
    intro s t hst
    obtain ⟨h0, h2⟩ := hlad s (t * polar QN b c) (by rwa [mul_smul])
    exact ⟨h0, (mul_eq_zero.mp h2).resolve_right hβ⟩
  exact (isOrthA2_eichler hs.ndN ha (by rw [map_smul_eq_sq, hd, mul_zero])
    (by rw [polar_smul_right_eq, had, mul_zero]) hli).1.ne_one h1

theorem sigmaGroup_le_elementaryGroup [FiniteDimensional K' N]
    (hnd : (polarBilin QN).Nondegenerate) (π : Submodule K' N) :
    sigmaGroup QN π ≤ elementaryGroup QN := by
  rw [sigmaGroup, Subgroup.closure_le]
  rintro s ⟨hs, -⟩
  exact (IsLongRootElement.isOrthA2 hnd hs).mem_elementaryGroup hnd

omit [CharP K 2] in
theorem OmegaSetting.isSiegelFamily_map [Finite K'] [FiniteDimensional K' N]
    (hs : OmegaSetting QN Qf ρ) {π : Submodule K' N} (hπ : ∀ w ∈ π, QN w = 0)
    (hπ3 : finrank K' π = 3) :
    IsSiegelFamily Qf (((sigmaGroup QN π).subgroupOf (elementaryGroup QN)).map ρ) := by
  have hndN' : ∀ x : N, (∀ y, polar QN x y = 0) → x = 0 := fun x hx => hs.ndN.1 x fun y => hx y
  have hle := sigmaGroup_le_elementaryGroup hs.ndN π
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨s, hs', rfl⟩ _ ⟨t, ht', rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext (sigmaGroup_mul_comm hndN' hπ hs' ht'))
  · rw [Subgroup.card_map_of_injective hs.inj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      natCard_sigmaGroup hndN' hπ hπ3, hs.card]
  · rintro _ ⟨s, hs', rfl⟩ hs1
    have hs1' : (s : N ≃ₗ[K'] N) ≠ 1 := fun h =>
      hs1 (by rw [show s = 1 from Subtype.ext h, map_one])
    have := (mem_sigmaGroup_iff_of_ne_one hndN' hπ hπ3 hs1').mp hs'
    exact hs.siegel s (IsLongRootElement.isOrthA2 hs.ndN this.1)

omit [CharP K 2] in
private theorem commutatorSpace_range_le' {L : Type*} [Group L] (ψ : L →* (V ≃ₗ[K] V))
    {S : Set L} (hS : Subgroup.closure S = ⊤) {U : Submodule K V}
    (hU : ∀ s ∈ S, movedSpace (ψ s) ≤ U) : commutatorSpace ψ.range ≤ U := by
  let H : Subgroup (V ≃ₗ[K] V) :=
    { carrier := {g | ∀ v, g v - v ∈ U}
      one_mem' := fun v => by simp
      mul_mem' := fun {g h} hg hh v => by
        have e : (g * h) v - v = (g (h v) - h v) + (h v - v) := by
          rw [LinearEquiv.mul_apply]
          abel
        rw [e]
        exact U.add_mem (hg _) (hh v)
      inv_mem' := fun {g} hg v => by
        have h1 : g (g⁻¹ v) = v := by simp
        have e : g⁻¹ v - v = -(g (g⁻¹ v) - g⁻¹ v) := by
          rw [h1]
          abel
        rw [e]
        exact U.neg_mem (hg _) }
  have hcl : Subgroup.closure S ≤ H.comap ψ := by
    rw [Subgroup.closure_le]
    intro s hs v
    exact hU s hs (sub_mem_movedSpace (ψ s) v)
  rw [hS] at hcl
  rw [commutatorSpace, Submodule.span_le]
  rintro w ⟨h, ⟨g, rfl⟩, v, rfl⟩
  exact hcl (Subgroup.mem_top g) v

omit [CharP K' 2] [CharP K 2] in
theorem top_le_iSup_of_generate (htop : commutatorSpace ρ.range = ⊤) {ι : Type*}
    (a b : ι → N)
    (hgen : elementaryGroup QN ≤
      Subgroup.closure {g | ∃ i, ∃ c : K', g = eichler QN (a i) (c • b i)})
    {A : ι → Submodule K V} (hA : ∀ i, ∀ c : K', movedSpace (rhoE ρ (a i) (c • b i)) ≤ A i) :
    (⊤ : Submodule K V) ≤ ⨆ i, A i := by
  set S : Set ↥(elementaryGroup QN) :=
    {g | ∃ i, ∃ c : K', (g : N ≃ₗ[K'] N) = eichler QN (a i) (c • b i)} with hS
  have himg : (elementaryGroup QN).subtype '' S =
      {g | ∃ i, ∃ c : K', g = eichler QN (a i) (c • b i)} := by
    ext g
    constructor
    · rintro ⟨h, ⟨i, c, hh⟩, rfl⟩
      exact ⟨i, c, hh⟩
    · rintro ⟨i, c, rfl⟩
      exact ⟨⟨eichler QN (a i) (c • b i), eichler_mem_elementaryGroup QN _ _⟩, ⟨i, c, rfl⟩, rfl⟩
  have hclos : Subgroup.closure S = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have h1 : (g : N ≃ₗ[K'] N) ∈ Subgroup.closure ((elementaryGroup QN).subtype '' S) := by
      rw [himg]
      exact hgen g.2
    rw [← MonoidHom.map_closure] at h1
    obtain ⟨h, hh, hhg⟩ := h1
    rwa [show h = g from Subtype.ext hhg] at hh
  have hle := commutatorSpace_range_le' ρ hclos (U := ⨆ i, A i) (by
    rintro s ⟨i, c, hs⟩
    rw [show s = ⟨eichler QN (a i) (c • b i), eichler_mem_elementaryGroup QN _ _⟩ from
      Subtype.ext hs]
    exact (hA i c).trans (le_iSup A i))
  rwa [htop] at hle

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel
