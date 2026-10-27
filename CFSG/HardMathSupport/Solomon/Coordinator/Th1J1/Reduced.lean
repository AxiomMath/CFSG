module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedGeneral
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Triple
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem isElemAbelian_omegaOneZ' (X : Subgroup G) : IsElemAbelian 2 (omegaOneZ X) := by
  refine IsElemAbelian.closure_of_commute ?_ ?_
  · rintro a ⟨ha, _⟩ b ⟨hb, _⟩
    exact (Sec7.mem_centerOf_iff'.1 ha).2 b (Sec7.mem_centerOf_iff'.1 hb).1
  · rintro a ⟨_, ha2⟩
    exact ha2

omit [Finite G] in
private theorem conj_mem_centralizer_of_normalizer {U : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (U : Set G)) {n : G}
    (hn : n ∈ Subgroup.centralizer (U : Set G)) :
    g * n * g⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hn ⊢
  intro u hu
  have hv : g⁻¹ * u * g ∈ U := by
    have h1 : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
    exact (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * u * g)).2 (by rw [h1]; exact hu)
  have key := hn (g⁻¹ * u * g) hv
  calc u * (g * n * g⁻¹) = g * ((g⁻¹ * u * g) * n) * g⁻¹ := by group
    _ = g * (n * (g⁻¹ * u * g)) * g⁻¹ := by rw [key]
    _ = g * n * g⁻¹ * u := by group

omit [Finite G] in
private theorem closure_comm_of_gens {gens : Set G} {k : G} (h : ∀ g ∈ gens, g * k = k * g) :
    ∀ u ∈ Subgroup.closure gens, u * k = k * u := by
  intro u hu
  induction hu using Subgroup.closure_induction with
  | mem g hg => exact h g hg
  | one => simp
  | mul a b _ _ ha hb =>
    calc a * b * k = a * (b * k) := mul_assoc _ _ _
      _ = a * (k * b) := by rw [hb]
      _ = a * k * b := (mul_assoc _ _ _).symm
      _ = k * a * b := by rw [ha]
      _ = k * (a * b) := mul_assoc _ _ _
  | inv a _ ha =>
    calc a⁻¹ * k = a⁻¹ * (k * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * k) * a⁻¹ := by rw [← ha]
      _ = k * a⁻¹ := by group

omit [Finite G] in
private theorem closure_conj_mem {R : Subgroup G} {gens : Set G}
    (hgen : ∀ g ∈ R, ∀ x ∈ gens, g * x * g⁻¹ ∈ gens) :
    ∀ g ∈ R, ∀ u ∈ Subgroup.closure gens, g * u * g⁻¹ ∈ Subgroup.closure gens := by
  intro g hg u hu
  induction hu using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (hgen g hg x hx)
  | one => simp
  | mul a b _ _ ha hb =>
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact mul_mem ha hb
  | inv a _ ha =>
    have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ha

private theorem exists_sylow_subgroupOf_of_odd {R S : Subgroup G} (hSR : S ≤ R)
    (hS : IsPGroup 2 S) (hodd : ¬ 2 ∣ S.relIndex R) :
    ∃ T : Sylow 2 R, (T : Subgroup R) = S.subgroupOf R := by
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  have hcard : Nat.card (S.subgroupOf R) = 2 ^ n := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSR).toEquiv, hn]
  have hmul : Nat.card (S.subgroupOf R) * S.relIndex R = Nat.card R :=
    Subgroup.card_mul_index (S.subgroupOf R)
  have hidx0 : S.relIndex R ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    exact (Nat.card_pos (α := R)).ne' hmul.symm
  have hfac : (Nat.card R).factorization 2 = n := by
    rw [← hmul, hcard, Nat.factorization_mul (pow_ne_zero n two_ne_zero) hidx0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hodd, add_zero]
  exact ⟨Sylow.ofCard (S.subgroupOf R) (by rw [hcard, hfac]), Sylow.coe_ofCard _ _⟩

theorem exists_reduced {R S H : Subgroup G} (hSR : S ≤ R) (hS : IsPGroup 2 S)
    (hSyl : ¬ 2 ∣ S.relIndex R) (hHS : H ≤ S) (hHn : R ≤ Subgroup.normalizer (H : Set G))
    (hHc : ∀ x ∈ R, (∀ h ∈ H, h * x = x * h) → x ∈ H) :
    ∃ U : Subgroup G, U ≤ R ∧ R ≤ Subgroup.normalizer (U : Set G) ∧ IsElemAbelian 2 U ∧
      omegaOneZ S ≤ U ∧ U ≤ H ∧ H ≤ Subgroup.centralizer (U : Set G) ∧
      ∀ K : Subgroup G, K ≤ R → R ≤ Subgroup.normalizer (K : Set G) →
        (∀ k ∈ K, ∃ n : ℕ, k ^ (2 ^ n) ∈ Subgroup.centralizer (U : Set G)) →
        K ≤ Subgroup.centralizer (U : Set G) := by
  have hZS : omegaOneZ S ≤ S := Sec7.omegaOneZ_le S
  have hZR : omegaOneZ S ≤ R := hZS.trans hSR
  have hZcen : omegaOneZ S ≤ centerOf S := (Subgroup.closure_le _).2 fun _ hx => hx.1
  have hZcomm : ∀ z ∈ omegaOneZ S, ∀ y ∈ S, z * y = y * z := fun z hz y hy =>
    (Sec7.mem_centerOf_iff'.1 (hZcen hz)).2 y hy
  have hZsq : ∀ z ∈ omegaOneZ S, z ^ 2 = 1 := (isElemAbelian_omegaOneZ' S).2
  obtain ⟨gens, hgens⟩ : ∃ gens : Set G,
      gens = {g | ∃ r ∈ R, ∃ z ∈ omegaOneZ S, g = r * z * r⁻¹} := ⟨_, rfl⟩
  have hmem : ∀ g, g ∈ gens ↔ ∃ r ∈ R, ∃ z ∈ omegaOneZ S, g = r * z * r⁻¹ := by
    intro g
    rw [hgens]
    exact Iff.rfl
  have hgenR : ∀ g ∈ gens, g ∈ R := by
    intro g hg
    obtain ⟨r, hr, z, hz, rfl⟩ := (hmem g).1 hg
    exact R.mul_mem (R.mul_mem hr (hZR hz)) (R.inv_mem hr)
  have hZH : ∀ z ∈ omegaOneZ S, z ∈ H := fun z hz =>
    hHc z (hZR hz) fun h hh => (hZcomm z hz h (hHS hh)).symm
  have hgenH : ∀ g ∈ gens, g ∈ H := by
    intro g hg
    obtain ⟨r, hr, z, hz, rfl⟩ := (hmem g).1 hg
    exact (Subgroup.mem_normalizer_iff.1 (hHn hr) z).1 (hZH z hz)
  have hgenC : ∀ g ∈ gens, ∀ h ∈ H, h * g = g * h := by
    intro g hg h hh
    obtain ⟨r, hr, z, hz, rfl⟩ := (hmem g).1 hg
    have hw : r⁻¹ * h * r ∈ H := by
      have := (Subgroup.mem_normalizer_iff.1 (hHn (R.inv_mem hr)) h).1 hh
      rwa [inv_inv] at this
    have hzw : (r⁻¹ * h * r) * z = z * (r⁻¹ * h * r) := (hZcomm z hz _ (hHS hw)).symm
    calc h * (r * z * r⁻¹) = r * ((r⁻¹ * h * r) * z) * r⁻¹ := by group
      _ = r * (z * (r⁻¹ * h * r)) * r⁻¹ := by rw [hzw]
      _ = r * z * r⁻¹ * h := by group
  have hgenSq : ∀ g ∈ gens, g ^ 2 = 1 := by
    intro g hg
    obtain ⟨r, hr, z, hz, rfl⟩ := (hmem g).1 hg
    rw [conj_pow, hZsq z hz]
    group
  have hgenComm : ∀ a ∈ gens, ∀ b ∈ gens, a * b = b * a := fun a ha b hb =>
    (hgenC a ha b (hgenH b hb)).symm
  have hgenConj : ∀ g ∈ R, ∀ x ∈ gens, g * x * g⁻¹ ∈ gens := by
    intro g hg x hx
    obtain ⟨r, hr, z, hz, rfl⟩ := (hmem _).1 hx
    refine (hmem _).2 ⟨g * r, R.mul_mem hg hr, z, hz, ?_⟩
    group
  have hconj := closure_conj_mem hgenConj
  have hZU : omegaOneZ S ≤ Subgroup.closure gens := by
    intro z hz
    exact Subgroup.subset_closure ((hmem z).2 ⟨1, R.one_mem, z, hz, by group⟩)
  have hRN : R ≤ Subgroup.normalizer ((Subgroup.closure gens : Subgroup G) : Set G) := by
    intro g hg
    refine Sec7.mem_normalizer_of_conj_mem (fun x hx => hconj g hg x hx) (fun x hx => ?_)
    have := hconj g⁻¹ (R.inv_mem hg) x hx
    rwa [inv_inv] at this
  have hHcent : H ≤ Subgroup.centralizer ((Subgroup.closure gens : Subgroup G) : Set G) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    exact closure_comm_of_gens (fun g hg => (hgenC g hg h hh).symm)
  refine ⟨Subgroup.closure gens, (Subgroup.closure_le R).2 (fun g hg => hgenR g hg), hRN,
    IsElemAbelian.closure_of_commute hgenComm hgenSq, hZU,
    (Subgroup.closure_le H).2 (fun g hg => hgenH g hg), hHcent, ?_⟩
  intro K hKR hKn hKpow
  obtain ⟨T, hT⟩ := exists_sylow_subgroupOf_of_odd hSR hS hSyl
  haveI hCN : ((Subgroup.centralizer ((Subgroup.closure gens : Subgroup G) : Set G)).subgroupOf R).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using conj_mem_centralizer_of_normalizer (hRN g.2) hn⟩
  haveI hDN : (K.subgroupOf R).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using (Subgroup.mem_normalizer_iff.1 (hKn g.2) (n : G)).1 hn⟩
  have hZc : ∀ z ∈ (omegaOneZ S).subgroupOf R, ∀ t ∈ (T : Subgroup R), t * z = z * t := by
    intro z hz t ht
    rw [hT] at ht
    apply Subtype.ext
    have h1 := hZcomm (z : G) (Subgroup.mem_subgroupOf.1 hz) (t : G) (Subgroup.mem_subgroupOf.1 ht)
    simpa using h1.symm
  have hCZ : (Subgroup.centralizer ((Subgroup.closure gens : Subgroup G) : Set G)).subgroupOf R ≤
      Subgroup.centralizer (((omegaOneZ S).subgroupOf R : Subgroup R) : Set R) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    apply Subtype.ext
    have h1 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 hc) (z : G)
      (hZU (Subgroup.mem_subgroupOf.1 hz))
    simpa using h1
  have hDp : ∀ d ∈ K.subgroupOf R, ∃ k : ℕ,
      d ^ 2 ^ k ∈ (Subgroup.centralizer ((Subgroup.closure gens : Subgroup G) : Set G)).subgroupOf R := by
    intro d hd
    obtain ⟨k, hk⟩ := hKpow (d : G) (Subgroup.mem_subgroupOf.1 hd)
    exact ⟨k, Subgroup.mem_subgroupOf.2 (by rw [Subgroup.coe_pow]; exact hk)⟩
  have hcentral := CFSG.QuasithinUnique.Setup.normal_le_centralizer_of_pPower 2 T hZc hCZ hDp
  have hstep : ∀ k ∈ K, ∀ z ∈ omegaOneZ S, k * z = z * k := by
    intro k hk z hz
    have hkD : (⟨k, hKR hk⟩ : R) ∈ K.subgroupOf R := Subgroup.mem_subgroupOf.2 hk
    have hzZ : (⟨z, hZR hz⟩ : R) ∈ (omegaOneZ S).subgroupOf R := Subgroup.mem_subgroupOf.2 hz
    have h1 := Subgroup.mem_centralizer_iff.1 (hcentral hkD) ⟨z, hZR hz⟩ hzZ
    have h2 := congrArg Subtype.val h1
    simpa using h2.symm
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  refine closure_comm_of_gens ?_
  intro g hg
  obtain ⟨r, hr, z, hz, rfl⟩ := (hmem g).1 hg
  have hk' : r⁻¹ * k * r ∈ K := by
    have := (Subgroup.mem_normalizer_iff.1 (hKn (R.inv_mem hr)) k).1 hk
    rwa [inv_inv] at this
  calc r * z * r⁻¹ * k = r * (z * (r⁻¹ * k * r)) * r⁻¹ := by group
    _ = r * ((r⁻¹ * k * r) * z) * r⁻¹ := by rw [hstep _ hk' z hz]
    _ = k * (r * z * r⁻¹) := by group

end CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1
