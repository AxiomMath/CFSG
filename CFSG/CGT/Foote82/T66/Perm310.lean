module

public import CFSG.Fischer.Classification.Recognition.SpUBasic
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltInv

public section

namespace CFSG.CGT.Foote82

open CFSG.Open

@[expose] def altOn {m : ℕ} (F : Set (Fin m)) : Subgroup (Equiv.Perm (Fin m)) :=
  alternatingGroup (Fin m) ⊓ fixingSubgroup (Equiv.Perm (Fin m)) Fᶜ

namespace Perm310

open Equiv Equiv.Perm MulAction

variable {m : ℕ}

private theorem inv_apply_self' (f : Perm (Fin m)) (x : Fin m) : f⁻¹ (f x) = x :=
  f.symm_apply_apply x

private theorem apply_inv_self' (f : Perm (Fin m)) (x : Fin m) : f (f⁻¹ x) = x :=
  f.apply_symm_apply x

private theorem comm_apply {R : Subgroup (Perm (Fin m))} {g : Perm (Fin m)}
    (hg : g ∈ Subgroup.centralizer (R : Set (Perm (Fin m)))) {r : Perm (Fin m)} (hr : r ∈ R)
    (y : Fin m) : g (r y) = r (g y) :=
  (congrArg (fun f : Perm (Fin m) => f y) (Subgroup.mem_centralizer_iff.1 hg r hr)).symm

private theorem fixed_apply {R : Subgroup (Perm (Fin m))} {g : Perm (Fin m)}
    (hg : g ∈ Subgroup.centralizer (R : Set (Perm (Fin m)))) {y : Fin m}
    (hy : ∀ r ∈ R, r y = y) : ∀ r ∈ R, r (g y) = g y := fun r hr => by
  rw [← comm_apply hg hr, hy r hr]

private theorem not_fixed_apply {R : Subgroup (Perm (Fin m))} {g : Perm (Fin m)}
    (hg : g ∈ Subgroup.centralizer (R : Set (Perm (Fin m)))) {y : Fin m}
    (hy : ¬ ∀ r ∈ R, r y = y) : ¬ ∀ r ∈ R, r (g y) = g y := fun h => hy (by
  have := fixed_apply (Subgroup.inv_mem _ hg) h
  simpa only [inv_apply_self'] using this)

private def orbB (R : Subgroup (Perm (Fin m))) : Subgroup (Perm (Fin m)) where
  carrier := {g | g ∈ Subgroup.centralizer (R : Set (Perm (Fin m))) ∧ ∀ i, ∃ r ∈ R, g i = r i}
  one_mem' := ⟨Subgroup.one_mem _, fun _ => ⟨1, R.one_mem, rfl⟩⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Subgroup.mul_mem _ ha hb, fun i => ?_⟩
    obtain ⟨s, hs, hsi⟩ := hb' i
    obtain ⟨r, hr, hri⟩ := ha' i
    refine ⟨s * r, R.mul_mem hs hr, ?_⟩
    rw [Perm.mul_apply, Perm.mul_apply, hsi, comm_apply ha hs, hri]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨Subgroup.inv_mem _ ha, fun i => ?_⟩
    obtain ⟨r, hr, hri⟩ := ha' (a⁻¹ i)
    refine ⟨r⁻¹, R.inv_mem hr, ?_⟩
    rw [apply_inv_self'] at hri
    exact (Perm.inv_eq_iff_eq.2 hri).symm

private theorem orbB_le (R : Subgroup (Perm (Fin m))) :
    orbB R ≤ Subgroup.centralizer (R : Set (Perm (Fin m))) := fun _ hg => hg.1

private theorem orbB_conj {R : Subgroup (Perm (Fin m))} {c b : Perm (Fin m)}
    (hc : c ∈ Subgroup.centralizer (R : Set (Perm (Fin m)))) (hb : b ∈ orbB R) :
    c * b * c⁻¹ ∈ orbB R := by
  obtain ⟨hb, hb'⟩ := hb
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hb) (Subgroup.inv_mem _ hc), fun i => ?_⟩
  obtain ⟨r, hr, hri⟩ := hb' (c⁻¹ i)
  refine ⟨r, hr, ?_⟩
  rw [Perm.mul_apply, Perm.mul_apply, hri, comm_apply hc hr, apply_inv_self']

private theorem pow_apply_of_commute {g r : Perm (Fin m)} (hc : Commute g r) {x : Fin m}
    (h : g x = r x) (n : ℕ) : (g ^ n) x = (r ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ, Perm.mul_apply, Perm.mul_apply, ih, ← h]
    exact congrArg (fun f : Perm (Fin m) => f x) (hc.pow_right n).eq

private theorem pow_card_eq_one_of_mem {R : Subgroup (Perm (Fin m))} {r : Perm (Fin m)}
    (hr : r ∈ R) : r ^ Nat.card R = 1 := by
  have h := congrArg Subtype.val (pow_card_eq_one' (x := (⟨r, hr⟩ : R)))
  rwa [Subgroup.coe_pow, Subgroup.coe_one] at h

private theorem pow_card_apply {R : Subgroup (Perm (Fin m))} {g : Perm (Fin m)}
    (hg : g ∈ Subgroup.centralizer (R : Set (Perm (Fin m)))) {x : Fin m}
    (hx : ∃ r ∈ R, g x = r x) : (g ^ Nat.card R) x = x := by
  obtain ⟨r, hr, hrx⟩ := hx
  have hc : Commute g r := (Subgroup.mem_centralizer_iff.1 hg r hr).symm
  rw [pow_apply_of_commute hc hrx, pow_card_eq_one_of_mem hr, Perm.one_apply]

private theorem isPGroup_orbB {R : Subgroup (Perm (Fin m))} (hR : IsPGroup 2 R) :
    IsPGroup 2 (orbB R) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hR
  intro b
  refine ⟨n, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, ← hn, Subgroup.coe_one]
  exact Perm.ext fun i => pow_card_apply b.2.1 (b.2.2 i)

private theorem exists_orbB_ne_one {R : Subgroup (Perm (Fin m))} (hR : IsPGroup 2 R) {x : Fin m}
    (hx : ¬ ∀ r ∈ R, r x = x) :
    ∃ z ∈ orbB R, z ≠ 1 ∧ ∀ y, z y ≠ y → y ∈ orbit R x := by
  classical
  let φ : R →* Perm (orbit R x) := MulAction.toPermHom R (orbit R x)
  have hφ : ∀ (r : R) (y : orbit R x), ((φ r y : orbit R x) : Fin m) = (r : Perm (Fin m)) y :=
    fun _ _ => rfl
  have hP : IsPGroup 2 φ.range := hR.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hnt : Nontrivial φ.range := by
    obtain ⟨r, hr, hrx⟩ : ∃ r ∈ R, r x ≠ x := by
      by_contra h
      exact hx fun r hr => by_contra fun h' => h ⟨r, hr, h'⟩
    refine ⟨⟨⟨φ ⟨r, hr⟩, ⟨_, rfl⟩⟩, 1, fun h => hrx ?_⟩⟩
    have := congrArg
      (fun f : φ.range => (((f : Perm (orbit R x)) ⟨x, mem_orbit_self x⟩ : orbit R x) : Fin m)) h
    simpa only [hφ, Subgroup.coe_one, Perm.one_apply] using this
  have := hP.center_nontrivial
  obtain ⟨w, hw⟩ := exists_ne (1 : Subgroup.center φ.range)
  obtain ⟨r₀, hr₀⟩ := (w : φ.range).2
  set σ : Perm (orbit R x) := ((w : φ.range) : Perm (orbit R x))
  have hσy : ∀ y (hy : y ∈ orbit R x), ((σ ⟨y, hy⟩ : orbit R x) : Fin m) = (r₀ : Perm (Fin m)) y :=
    fun y hy => by rw [← hr₀]; rfl
  have hσc : ∀ r : R, φ r * σ = σ * φ r := fun r => by
    have h := Subgroup.mem_center_iff.1 w.2 ⟨φ r, ⟨r, rfl⟩⟩
    exact congrArg Subtype.val h
  have hmem : ∀ (r : Perm (Fin m)) (hr : r ∈ R) {y : Fin m}, y ∈ orbit R x → r y ∈ orbit R x :=
    fun r hr y hy => mapsTo_smul_orbit (⟨r, hr⟩ : R) x hy
  have hnmem : ∀ (r : Perm (Fin m)) (hr : r ∈ R) {y : Fin m}, y ∉ orbit R x → r y ∉ orbit R x :=
    fun r hr y hy h => hy (by
      have := hmem r⁻¹ (R.inv_mem hr) h
      rwa [inv_apply_self'] at this)
  refine ⟨ofSubtype σ, ⟨Subgroup.mem_centralizer_iff.2 fun r hr => ?_, fun i => ?_⟩, ?_, ?_⟩
  · refine Perm.ext fun y => ?_
    rw [Perm.mul_apply, Perm.mul_apply]
    by_cases hy : y ∈ orbit R x
    · rw [ofSubtype_apply_of_mem σ hy, ofSubtype_apply_of_mem σ (hmem r hr hy)]
      have h := congrArg (fun f : Perm (orbit R x) => ((f ⟨y, hy⟩ : orbit R x) : Fin m))
        (hσc ⟨r, hr⟩)
      exact h
    · rw [ofSubtype_apply_of_not_mem σ hy, ofSubtype_apply_of_not_mem σ (hnmem r hr hy)]
  · by_cases hi : i ∈ orbit R x
    · exact ⟨r₀, r₀.2, by rw [ofSubtype_apply_of_mem σ hi, hσy i hi]⟩
    · exact ⟨1, R.one_mem, by rw [ofSubtype_apply_of_not_mem σ hi, Perm.one_apply]⟩
  · intro h
    apply hw
    have h1 : σ = 1 := ofSubtype_injective (h.trans (map_one _).symm)
    exact Subtype.ext (Subtype.ext h1)
  · intro y hy
    by_contra hyO
    exact hy (ofSubtype_apply_of_not_mem σ hyO)

private theorem exists_apply_eq {R : Subgroup (Perm (Fin m))} (hR : IsPGroup 2 R)
    {k : Perm (Fin m)} (hkC : k ∈ Subgroup.centralizer (R : Set (Perm (Fin m))))
    (hkB : ∀ b ∈ orbB R, k * b = b * k) {x : Fin m} (hx : ¬ ∀ r ∈ R, r x = x) :
    ∃ r ∈ R, k x = r x := by
  obtain ⟨z, hzB, hz1, hzO⟩ := exists_orbB_ne_one hR hx
  obtain ⟨y, hy⟩ : ∃ y, z y ≠ y := by
    by_contra h
    exact hz1 (Perm.ext fun y => not_not.1 (not_exists.1 h y))
  have hkyO : k y ∈ orbit R x := by
    refine hzO _ fun h => hy (k.injective ?_)
    have h2 : (k * z) y = (z * k) y := by rw [hkB z hzB]
    rwa [Perm.mul_apply, Perm.mul_apply, h] at h2
  obtain ⟨⟨s, hs⟩, hsy⟩ := mem_orbit_iff.1 (hzO y hy)
  obtain ⟨⟨t, ht⟩, hty⟩ := mem_orbit_iff.1 hkyO
  have hsy' : s x = y := hsy
  have hty' : t x = k y := hty
  refine ⟨s⁻¹ * t, R.mul_mem (R.inv_mem hs) ht, ?_⟩
  rw [Perm.mul_apply, hty', ← hsy', comm_apply hkC hs, inv_apply_self']

private theorem eq_top_of_pow_mem {G : Type*} [Group G] [Finite G] [Group.IsPerfect G] {p : ℕ}
    [Fact p.Prime] {N : Subgroup G} [N.Normal] {n : ℕ} (h : ∀ g : G, g ^ p ^ n ∈ N) : N = ⊤ := by
  by_contra hN
  have hQ : IsPGroup p (G ⧸ N) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨n, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact h g⟩
  have : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.2 hN
  exact Group.IsPerfect.not_isNilpotent (G ⧸ N) hQ.isNilpotent

private theorem altOn_le_centralizer (R : Subgroup (Perm (Fin m))) :
    altOn {i | ∀ r ∈ R, r i = i} ≤ Subgroup.centralizer (R : Set (Perm (Fin m))) := by
  intro g hg
  have hfix : ∀ y, ¬ (∀ r ∈ R, r y = y) → g y = y := fun y hy =>
    (mem_fixingSubgroup_iff _).1 hg.2 y hy
  refine Subgroup.mem_centralizer_iff.2 fun r hr => Perm.ext fun y => ?_
  rw [Perm.mul_apply, Perm.mul_apply]
  by_cases hy : ∀ r ∈ R, r y = y
  · have hgy : ∀ s ∈ R, s (g y) = g y := by
      by_contra hgy
      have h2 : g y = y := g.injective (hfix _ hgy)
      rw [h2] at hgy
      exact hgy hy
    rw [hgy r hr, hy r hr]
  · have hry : ¬ ∀ s ∈ R, s (r y) = r y := fun h => hy (by
      have h1 : r y = y := r.injective (h r hr)
      rwa [h1] at h)
    rw [hfix y hy, hfix (r y) hry]

private theorem le_alternatingGroup {K : Subgroup (Perm (Fin m))} (hK : commutator K = ⊤) :
    K ≤ alternatingGroup (Fin m) := by
  intro k hk
  have h1 := Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp K.subtype)
  rw [hK] at h1
  have h2 := MonoidHom.mem_ker.1 (h1 (Subgroup.mem_top ⟨k, hk⟩))
  exact Equiv.Perm.mem_alternatingGroup.2 h2

private theorem altOn_eq_ghInv (S : Set (Fin m)) [DecidablePred (· ∈ S)] :
    altOn S = CFSG.GH74.GLS.IVK.GHInv.altOn (Finset.univ.filter (· ∈ S)) := by
  ext g
  rw [CFSG.GH74.GLS.IVK.GHInv.mem_altOn, altOn, Subgroup.mem_inf, mem_fixingSubgroup_iff,
    Equiv.Perm.mem_alternatingGroup, and_comm]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_compl_iff, Perm.smul_def]

end Perm310

open Perm310 in
theorem eq_altOn_of_isComponentOf {m : ℕ} {R X K : Subgroup (Equiv.Perm (Fin m))}
    (hR : IsPGroup 2 R)
    (hX₁ : alternatingGroup (Fin m) ⊓ Subgroup.centralizer (R : Set (Equiv.Perm (Fin m))) ≤ X)
    (hX₂ : X ≤ Subgroup.centralizer (R : Set (Equiv.Perm (Fin m)))) (hK : IsComponentOf K X) :
    5 ≤ Nat.card {i : Fin m // ∀ r ∈ R, r i = i} ∧ K = altOn {i | ∀ r ∈ R, r i = i} := by
  classical
  set C := Subgroup.centralizer (R : Set (Equiv.Perm (Fin m)))
  have hXn : (X.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hX₂]
    intro x c hx hc
    have hcomm : c * x * c⁻¹ * x⁻¹ ∈ X := by
      refine hX₁ ⟨Equiv.Perm.mem_alternatingGroup.2 ?_, ?_⟩
      · simp only [map_mul, map_inv]
        rw [mul_right_comm (Equiv.Perm.sign c), mul_inv_cancel, one_mul, mul_inv_cancel]
      · exact C.mul_mem (C.mul_mem (C.mul_mem hc (hX₂ hx)) (C.inv_mem hc)) (C.inv_mem (hX₂ hx))
    simpa only [inv_mul_cancel_right] using X.mul_mem hcomm hx
  have hKC : IsComponentOf K C :=
    ⟨hK.1.trans hX₂, hK.2.1.trans (IsSubnormal.step hX₂ hXn (IsSubnormal.refl C)), hK.2.2⟩
  have hBsolv : Group.IsSolvable (orbB R) := by
    have := (isPGroup_orbB hR).isNilpotent
    infer_instance
  have hcomm := CFSG.Fischer.Classification.Recognition.SpU.commute_of_isComponentOf hKC
    (orbB_le R) (fun c hc b hb => orbB_conj hc hb) hBsolv
  have hKP : Group.IsPerfect K := ⟨hK.2.2.1⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hR
  have hKfix : K ≤ fixingSubgroup (Equiv.Perm (Fin m)) {i | ∀ r ∈ R, r i = i}ᶜ := by
    have hN : ((fixingSubgroup (Equiv.Perm (Fin m))
        {i | ∀ r ∈ R, r i = i}ᶜ).subgroupOf K).Normal := by
      refine ⟨fun a ha g => ?_⟩
      rw [Subgroup.mem_subgroupOf, mem_fixingSubgroup_iff] at ha ⊢
      intro y hy
      have hy' := not_fixed_apply (Subgroup.inv_mem _ (hKC.1 g.2)) hy
      have h1 := ha _ hy'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.smul_def,
        Equiv.Perm.mul_apply] at h1 ⊢
      rw [h1]
      exact (Equiv.Perm.inv_eq_iff_eq.1 rfl).symm
    have htop := eq_top_of_pow_mem (G := K) (p := 2) (n := n)
      (N := (fixingSubgroup (Equiv.Perm (Fin m)) {i | ∀ r ∈ R, r i = i}ᶜ).subgroupOf K)
      (fun k => by
        rw [Subgroup.mem_subgroupOf, mem_fixingSubgroup_iff, Subgroup.coe_pow, ← hn]
        intro y hy
        exact pow_card_apply (hKC.1 k.2)
          (exists_apply_eq hR (hKC.1 k.2) (fun b hb => hcomm k k.2 b hb) hy))
    exact Subgroup.subgroupOf_eq_top.1 htop
  have hKalt : K ≤ altOn {i | ∀ r ∈ R, r i = i} := fun k hk =>
    ⟨le_alternatingGroup hK.2.2.1 hk, hKfix hk⟩
  have haltX : altOn {i | ∀ r ∈ R, r i = i} ≤ X := fun g hg =>
    hX₁ ⟨hg.1, altOn_le_centralizer R hg⟩
  have hsub : IsSubnormal K (altOn {i | ∀ r ∈ R, r i = i}) := by
    have := hK.2.1.inf_of_le haltX
    rwa [inf_eq_left.2 hKalt] at this
  have hKne : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1
    (CFSG.LocalCores.isQuasisimple_nontrivial
      (CFSG.Fischer.Classification.Recognition.localCores_isQuasisimple hK.2.2))
  have hcard : Nat.card {i : Fin m // ∀ r ∈ R, r i = i} =
      (Finset.univ.filter (· ∈ {i : Fin m | ∀ r ∈ R, r i = i})).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  have h5 : 5 ≤ Nat.card {i : Fin m // ∀ r ∈ R, r i = i} := by
    by_contra h5
    have h5' := not_le.1 h5
    refine hKne (CFSG.GH74.GLS.IVK.GHInv.eq_bot_of_perfect_le_symOn
      (F := Finset.univ.filter (· ∈ {i : Fin m | ∀ r ∈ R, r i = i})) (by omega) hKP ?_)
    intro k hk y hy
    have := (mem_fixingSubgroup_iff _).1 (hKfix hk) y (by simpa using hy)
    exact this
  refine ⟨h5, ?_⟩
  have hsimple : IsSimpleGroup (altOn {i | ∀ r ∈ R, r i = i}) := by
    rw [altOn_eq_ghInv]
    exact CFSG.GH74.GLS.IVK.GHInv.isSimpleGroup_altOn (by omega)
  rcases hsub.eq_bot_or_eq_of_isSimpleGroup hsimple with h | h
  · exact absurd h hKne
  · exact h

end CFSG.CGT.Foote82
