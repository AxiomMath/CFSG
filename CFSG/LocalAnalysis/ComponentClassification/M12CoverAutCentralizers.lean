module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizerCheck
public import Certificates.Certificate11004

public section

namespace CFSG.ComponentClassification.M12Cover

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.OuterAutomorphisms

section General

variable {G H : Type*} [Group G] [Group H]

@[expose] def FourClassesLarge (G : Type*) [Group G] : Prop :=
  ∀ x : G, x ^ 4 = 1 → x ^ 2 ≠ 1 → 5 ≤ Nat.card {y : G // IsConj x y}

@[expose] def NoNormalFour (G : Type*) [Group G] : Prop :=
  ∀ N : Subgroup G, N.Normal → IsEmpty (N ≃* Multiplicative (ZMod 4)) ∧
    IsEmpty (N ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4))

theorem isConj_iff_of_mulEquiv (e : G ≃* H) (x y : G) : IsConj (e x) (e y) ↔ IsConj x y := by
  constructor
  · intro h
    simpa using e.symm.toMonoidHom.map_isConj h
  · exact e.toMonoidHom.map_isConj

theorem FourClassesLarge.of_mulEquiv (e : G ≃* H) (h : FourClassesLarge H) :
    FourClassesLarge G := by
  intro x hx4 hx2
  have h' := h (e x) (by rw [← map_pow, hx4, map_one]) (fun h2 => hx2 (e.injective (by
    rw [map_pow, h2, map_one])))
  refine h'.trans (le_of_eq (Nat.card_congr ?_))
  exact (e.toEquiv.subtypeEquiv fun y => (isConj_iff_of_mulEquiv e x y).symm).symm

theorem isEmpty_of_fourClassesLarge [Finite G] (hG : FourClassesLarge G) (N : Subgroup G)
    [N.Normal] {T : Type*} [Group T] [Finite T] (t₀ : T) (ht4 : t₀ ^ 4 = 1) (ht2 : t₀ ^ 2 ≠ 1)
    (hT : Nat.card {t : T // t ^ 2 ≠ 1} ≤ 4) : IsEmpty (N ≃* T) := by
  refine ⟨fun e => ?_⟩
  set x : G := ((e.symm t₀ : N) : G) with hxdef
  have hx4 : x ^ 4 = 1 := by
    rw [hxdef, ← SubgroupClass.coe_pow, ← map_pow, ht4, map_one, OneMemClass.coe_one]
  have hx2 : x ^ 2 ≠ 1 := by
    intro h
    apply ht2
    have : e.symm (t₀ ^ 2) = 1 := Subtype.ext (by
      rw [map_pow, SubgroupClass.coe_pow]
      exact h)
    simpa using congrArg e this
  have h5 := hG x hx4 hx2
  have hmem : ∀ y : G, IsConj x y → y ∈ N := by
    intro y hy
    obtain ⟨c, rfl⟩ := isConj_iff.1 hy
    exact Subgroup.Normal.conj_mem inferInstance _ (e.symm t₀).2 c
  let f : {y : G // IsConj x y} → {n : N // n ^ 2 ≠ 1} := fun y =>
    ⟨⟨y.1, hmem y.1 y.2⟩, fun h => by
      obtain ⟨c, hc⟩ := isConj_iff.1 y.2
      apply hx2
      have h' : (y.1 : G) ^ 2 = 1 := by simpa using congrArg Subtype.val h
      rw [← hc, conj_pow] at h'
      have h'' := congrArg (fun g => c⁻¹ * g * c) h'
      simpa [mul_assoc] using h''⟩
  have hf : Function.Injective f := fun a b hab => Subtype.ext (by
    have := congrArg (fun n : {n : N // n ^ 2 ≠ 1} => ((n.1 : N) : G)) hab
    simpa [f] using this)
  have hle := Nat.card_le_card_of_injective f hf
  have hNT : Nat.card {n : N // n ^ 2 ≠ 1} = Nat.card {t : T // t ^ 2 ≠ 1} :=
    Nat.card_congr (e.toEquiv.subtypeEquiv fun n => by
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ne_eq]
      constructor
      · intro h h'
        exact h (e.injective (by rw [map_pow, h', map_one]))
      · intro h h'
        exact h (by rw [← map_pow, h', map_one]))
  omega

theorem card_sq_ne_one_four : Nat.card {m : Multiplicative (ZMod 4) // m ^ 2 ≠ 1} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_sq_ne_one_two_four :
    Nat.card {m : Multiplicative (ZMod 2) × Multiplicative (ZMod 4) // m ^ 2 ≠ 1} = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem FourClassesLarge.noNormalFour [Finite G] (hG : FourClassesLarge G) : NoNormalFour G := by
  intro N hN
  refine ⟨isEmpty_of_fourClassesLarge hG N (Multiplicative.ofAdd 1) (by decide) (by decide)
    (by rw [card_sq_ne_one_four]; norm_num), isEmpty_of_fourClassesLarge hG N
    (1, Multiplicative.ofAdd 1) (by decide) (by decide) (by rw [card_sq_ne_one_two_four])⟩

@[expose] noncomputable def centralizerEquiv (e : G ≃* H) (t : G) :
    Subgroup.centralizer ({t} : Set G) ≃* Subgroup.centralizer ({e t} : Set H) :=
  ((Subgroup.centralizer ({t} : Set G)).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_centralizer_equiv e t))

@[expose] noncomputable def centralizerSubgroupEquiv (K : Subgroup G) (t : K) :
    Subgroup.centralizer ({t} : Set K) ≃* centralizerIn K (t : G) :=
  ((Subgroup.centralizer ({t} : Set K)).equivMapOfInjective K.subtype K.subtype_injective).trans
    (MulEquiv.subgroupCongr (map_centralizer_subtype K t))

@[expose] noncomputable def centralizerInConjEquiv (K : Subgroup G) {c : G} (hc : c ∈ K) (u : G) :
    centralizerIn K u ≃* centralizerIn K (c * u * c⁻¹) :=
  ((centralizerIn K u).equivMapOfInjective (MulAut.conj c).toMonoidHom
    (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr (centralizerIn_conj K hc u).symm)

end General

section Chain

variable {n : ℕ}

theorem listTables_spec (hn : n < 2 ^ 32) {K : Subgroup (Equiv.Perm (Fin n))}
    {gs : List (Equiv.Perm (Fin n))} (hgs : ∀ g ∈ gs, g ∈ K) :
    ∀ l < (listTables gs).size, Rep n (listTables gs)[l]! (gs.getD l 1) ∧
      Rep n (listTables (gs.map (·⁻¹)))[l]! (gs.getD l 1)⁻¹ ∧ gs.getD l 1 ∈ K := by
  intro l hl
  have hl' : l < gs.length := by simpa [listTables] using hl
  have h1 : (listTables gs)[l]! = toTable gs[l] := by
    rw [getElem!_pos (listTables gs) l hl]
    simp [listTables]
  have h2 : (listTables (gs.map (·⁻¹)))[l]! = toTable gs[l]⁻¹ := by
    rw [getElem!_pos (listTables (gs.map (·⁻¹))) l (by simpa [listTables] using hl')]
    simp [listTables]
  have h3 : gs.getD l 1 = gs[l] := by simp [List.getD_eq_getElem?_getD, hl']
  rw [h1, h2, h3]
  exact ⟨rep_toTable hn _, rep_toTable hn _, hgs _ (List.getElem_mem hl')⟩

theorem card_conj_eq_ncard (K : Subgroup (Equiv.Perm (Fin n))) (x : K) :
    Nat.card {y : K // IsConj x y} = (conjClass K (x : Equiv.Perm (Fin n))).ncard := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr
    { toFun := fun y => ⟨y.1, ?_⟩
      invFun := fun v => ⟨⟨v.1, ?_⟩, ?_⟩
      left_inv := fun y => rfl
      right_inv := fun v => rfl }
  · obtain ⟨c, hc⟩ := isConj_iff.1 y.2
    exact ⟨c, c.2, by rw [← hc]; rfl⟩
  · obtain ⟨c, hc, hv⟩ := v.2
    rw [hv]
    exact K.mul_mem (K.mul_mem hc x.2) (K.inv_mem hc)
  · obtain ⟨c, hc, hv⟩ := v.2
    exact isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext hv.symm⟩

theorem conjClass_conj (K : Subgroup (Equiv.Perm (Fin n))) {c : Equiv.Perm (Fin n)}
    (hc : c ∈ K) (r : Equiv.Perm (Fin n)) : conjClass K (c * r * c⁻¹) = conjClass K r := by
  ext v
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d * c, K.mul_mem hd hc, by group⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d * c⁻¹, K.mul_mem hd (K.inv_mem hc), by group⟩

theorem orderOf_eq_four {g : Equiv.Perm (Fin n)} (h4 : g ^ 4 = 1) (h2 : g ^ 2 ≠ 1) :
    orderOf g = 4 := by
  have hd : orderOf g ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have hd4 : orderOf g ∈ Nat.divisors 4 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
  have : Nat.divisors 4 = {1, 2, 4} := by decide
  rw [this] at hd4
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd4
  rcases hd4 with h | h | h
  · rw [orderOf_eq_one_iff] at h
    exact absurd (by rw [h, one_pow]) h2
  · exact absurd (by rw [← h, pow_orderOf_eq_one]) h2
  · exact h

theorem fourClassesLarge_of_repsOK (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (gs : List (Equiv.Perm (Fin n)))
    (hgs : ∀ g ∈ gs, g ∈ Q.originalSubgroup) (reps : List (Equiv.Perm (Fin n)))
    (hreps : ∀ r ∈ reps, r ∈ Q.originalSubgroup ∧ orderOf r = 4) (cap : ℕ)
    (hok : repsOK n (listTables gs) (listTables (gs.map (·⁻¹))) (cosetOrderTables Q 1 4)
      (reps.map toTable) cap = true)
    (hsz : ∀ r ∈ reps,
      5 ≤ (conjClosure n (listTables gs) (listTables (gs.map (·⁻¹))) (toTable r) cap).1.size) :
    FourClassesLarge Q.originalSubgroup := by
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn Q hQ (listTables_spec hn hgs) 1
    (fun h hh => by rw [inv_one, one_mul, mul_one]; exact hh) (by norm_num) reps
    (fun r hr => by simpa using hreps r hr) cap hok
  intro x hx4 hx2
  have hx4' : (x : Equiv.Perm (Fin n)) ^ 4 = 1 := by
    rw [← SubgroupClass.coe_pow, hx4, OneMemClass.coe_one]
  have hx2' : (x : Equiv.Perm (Fin n)) ^ 2 ≠ 1 := fun h => hx2 (Subtype.ext (by
    rw [SubgroupClass.coe_pow, h, OneMemClass.coe_one]))
  obtain ⟨r, hr, c, hc, hxr⟩ := hcov x (by simp) (orderOf_eq_four hx4' hx2')
  rw [card_conj_eq_ncard, hxr, conjClass_conj _ hc]
  exact (hsz r hr).trans (hsize r hr)

end Chain

theorem m12Rep1_eq : m12Rep1 = m12gA :=
  Certificates.certificate11004.1

theorem m12_reps_mem : ∀ r ∈ [m12Rep1, m12Rep2], r ∈ NativeSporadic.M12 ∧ orderOf r = 2 := by
  intro r hr
  obtain ⟨h1, h2, -⟩ := m12_rep_data1
  obtain ⟨h1', h2', -⟩ := m12_rep_data2
  rw [m12Certificate_originalSubgroup] at h1 h1'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨h1, h2⟩
  · exact ⟨h1', h2'⟩

theorem m12_involution_cover :
    (∀ u, 1⁻¹ * u ∈ NativeSporadic.M12 → orderOf u = 2 →
      ∃ r ∈ [m12Rep1, m12Rep2], ∃ c ∈ NativeSporadic.M12, u = c * r * c⁻¹) ∧
    ∀ r ∈ [m12Rep1, m12Rep2], (conjClosure 12 (pairTables m12gA m12gB)
      (pairTables m12gA⁻¹ m12gB⁻¹) (toTable r) 1000).1.size ≤
        (conjClass NativeSporadic.M12 r).ncard := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, -, -⟩ := m12_oddcore_cover
  rw [m12InvReps_eq] at hok
  have hA : m12gA ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  have hB : m12gB ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  have h := exists_conj_of_repsOK hn m12Certificate m12Certificate_check
    (pairTables_spec hn hA hB) 1 (fun h hh => by rw [inv_one, one_mul, mul_one]; exact hh)
    (by norm_num) [m12Rep1, m12Rep2] (fun r hr => by
      rw [inv_one, one_mul, m12Certificate_originalSubgroup]
      exact m12_reps_mem r hr) 1000 hok
  rw [m12Certificate_originalSubgroup] at h
  exact h

theorem centralizerIn_m12Rep1 :
    centralizerIn NativeSporadic.M12 m12Rep1 = m12CentQ1.originalSubgroup := by
  obtain ⟨-, -, hK, hKc, -⟩ := m12_rep_data1
  obtain ⟨-, hsz, -⟩ := m12_oddcore_cover
  rw [m12InvReps_eq] at hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [m12Certificate_originalSubgroup] at hK
  refine centralizerIn_eq_of_le _ _ hK (m12_involution_cover.2 _ (by simp)) ?_
  rw [hsz.1, hKc, m12_card]

theorem centralizerIn_m12Rep2 :
    centralizerIn NativeSporadic.M12 m12Rep2 = m12CentQ2.originalSubgroup := by
  obtain ⟨-, -, hK, hKc, -⟩ := m12_rep_data2
  obtain ⟨-, hsz, -⟩ := m12_oddcore_cover
  rw [m12InvReps_eq] at hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [m12Certificate_originalSubgroup] at hK
  refine centralizerIn_eq_of_le _ _ hK (m12_involution_cover.2 _ (by simp)) ?_
  rw [hsz.2, hKc, m12_card]

theorem card_centralizerIn_m12Rep1 : Nat.card (centralizerIn NativeSporadic.M12 m12Rep1) = 192 := by
  rw [centralizerIn_m12Rep1]
  exact m12_rep_data1.2.2.2.1

theorem card_centralizerIn_m12Rep2 : Nat.card (centralizerIn NativeSporadic.M12 m12Rep2) = 240 := by
  rw [centralizerIn_m12Rep2]
  exact m12_rep_data2.2.2.2.1

theorem fourClassesLarge_m12Rep1 : FourClassesLarge (centralizerIn NativeSporadic.M12 m12Rep1) := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  rw [centralizerIn_m12Rep1]
  have h := checkK1_eq
  simp only [checkK1, Bool.and_eq_true] at h
  obtain ⟨⟨hok, hsz⟩, hord⟩ := h
  have hgs : ∀ g ∈ k1Gens, g ∈ m12CentQ1.originalSubgroup := fun g hg => by
    rw [m12CentQ1, certificate_originalSubgroup]
    exact Subgroup.subset_closure hg
  refine fourClassesLarge_of_repsOK hn m12CentQ1 m12_oddcore_cent1.1 k1Gens hgs k1Reps
    (fun r hr => ⟨?_, ?_⟩) 1000 hok fun r hr => ?_
  · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
    exact evalCodes_mem _ hgs w
  · exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
      (List.all_eq_true.1 hord _ (List.mem_map_of_mem hr))
  · exact of_decide_eq_true (List.all_eq_true.1 hsz _
      (List.mem_map_of_mem (List.mem_map_of_mem hr)))

theorem fourClassesLarge_m12Rep2 : FourClassesLarge (centralizerIn NativeSporadic.M12 m12Rep2) := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  rw [centralizerIn_m12Rep2]
  have h := checkK3_eq
  simp only [checkK3, Bool.and_eq_true] at h
  obtain ⟨⟨hok, hsz⟩, hord⟩ := h
  have hgs : ∀ g ∈ k3Gens, g ∈ m12CentQ2.originalSubgroup := fun g hg => by
    rw [m12CentQ2, certificate_originalSubgroup]
    exact Subgroup.subset_closure hg
  refine fourClassesLarge_of_repsOK hn m12CentQ2 m12_oddcore_cent2.1 k3Gens hgs k3Reps
    (fun r hr => ⟨?_, ?_⟩) 1000 hok fun r hr => ?_
  · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
    exact evalCodes_mem _ hgs w
  · exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
      (List.all_eq_true.1 hord _ (List.mem_map_of_mem hr))
  · exact of_decide_eq_true (List.all_eq_true.1 hsz _
      (List.mem_map_of_mem (List.mem_map_of_mem hr)))

theorem card_le_two_mul_inf (H : Subgroup (Equiv.Perm (Fin 24))) (hH : H ≤ autModel) :
    Nat.card H ≤ 2 * Nat.card (H ⊓ blockGroup : Subgroup (Equiv.Perm (Fin 24))) := by
  have h1 := ((H ⊓ blockGroup).subgroupOf H).card_mul_index
  have h2 : Nat.card ((H ⊓ blockGroup).subgroupOf H) =
      Nat.card (H ⊓ blockGroup : Subgroup (Equiv.Perm (Fin 24))) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h3 : ((H ⊓ blockGroup).subgroupOf H).index ≤ 2 := by
    change (H ⊓ blockGroup).relIndex H ≤ 2
    rw [Subgroup.inf_relIndex_left]
    have h2' : blockGroup.relIndex autModel = 2 := index_blockGroup
    have := Subgroup.relIndex_le_of_le_right hH (H := blockGroup) (by rw [h2']; norm_num)
    rwa [h2'] at this
  rw [h2] at h1
  calc Nat.card H = Nat.card (H ⊓ blockGroup : Subgroup (Equiv.Perm (Fin 24))) *
        ((H ⊓ blockGroup).subgroupOf H).index := h1.symm
    _ ≤ Nat.card (H ⊓ blockGroup : Subgroup (Equiv.Perm (Fin 24))) * 2 :=
        Nat.mul_le_mul_left _ h3
    _ = 2 * Nat.card (H ⊓ blockGroup : Subgroup (Equiv.Perm (Fin 24))) := mul_comm _ _

theorem centralizerIn_autModel_inf (t : Equiv.Perm (Fin 24)) :
    centralizerIn autModel t ⊓ blockGroup = centralizerIn blockGroup t := by
  ext g
  simp only [Subgroup.mem_inf, mem_centralizerIn]
  constructor
  · rintro ⟨⟨-, h⟩, hD⟩
    exact ⟨hD, h⟩
  · rintro ⟨hD, h⟩
    exact ⟨⟨blockGroup_le_autModel hD, h⟩, hD⟩

theorem card_centralizer_eq_centralizerIn {n : ℕ} (K : Subgroup (Equiv.Perm (Fin n))) (t : K) :
    Nat.card (Subgroup.centralizer ({t} : Set K)) =
      Nat.card (centralizerIn K (t : Equiv.Perm (Fin n))) :=
  Nat.card_congr (centralizerSubgroupEquiv K t).toEquiv

theorem card_centralizerIn_blockGroup (g : NativeSporadic.M12) :
    Nat.card (centralizerIn blockGroup (m12EquivD g : Equiv.Perm (Fin 24))) =
      Nat.card (centralizerIn NativeSporadic.M12 (g : Equiv.Perm (Fin 12))) := by
  have h1 := map_centralizer_eq blockGroup m12EquivD.symm (m12EquivD g) (m12EquivD g).2
  have hg : m12EquivD.symm ⟨_, (m12EquivD g).2⟩ = g := by simp
  rw [hg] at h1
  have hinj : Function.Injective (blockGroup.subtype.comp m12EquivD.symm.symm.toMonoidHom) :=
    blockGroup.subtype_injective.comp m12EquivD.symm.symm.injective
  have e1 : Nat.card (centralizerIn NativeSporadic.M12 (g : Equiv.Perm (Fin 12))) =
      Nat.card (Subgroup.centralizer ({g} : Set NativeSporadic.M12)) :=
    (card_centralizer_eq_centralizerIn _ g).symm
  rw [e1, ← Subgroup.card_map_of_injective hinj, h1]
  rfl

theorem card_centralizerIn_autModel_le (g : NativeSporadic.M12) :
    Nat.card (centralizerIn autModel (m12EquivD g : Equiv.Perm (Fin 24))) ≤
      2 * Nat.card (centralizerIn NativeSporadic.M12 (g : Equiv.Perm (Fin 12))) := by
  have := card_le_two_mul_inf (centralizerIn autModel (m12EquivD g : Equiv.Perm (Fin 24)))
    inf_le_left
  rwa [centralizerIn_autModel_inf, card_centralizerIn_blockGroup] at this

theorem m12EquivD_m12a : (m12EquivD m12a : Equiv.Perm (Fin 24)) = m12A1 :=
  m12EquivD_apply (Subgroup.subset_closure (Set.mem_insert _ _))

theorem m12EquivD_elemZ : (m12EquivD elemZ : Equiv.Perm (Fin 24)) = blockHom (permZ, permZ) :=
  m12EquivD_apply pairs_permZ

theorem autModel_gens_mem : ∀ g ∈ [m12A1, m12B1], g ∈ autModel := by
  intro g hg
  exact blockGroup_le_autModel (m12_gens_memD g hg)

theorem modelGens_mem (ws : List (List ℤ)) :
    ∀ g ∈ ws.map (evalCodes [m12A1, m12B1]) ++ [m12Sigma], g ∈ autModel := by
  intro g hg
  rcases List.mem_append.1 hg with hg | hg
  · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
    exact evalCodes_mem _ autModel_gens_mem w
  · rw [List.mem_singleton.1 hg]
    exact sigma_mem_autModel

theorem gz_conj : permZ = evalCodes [m12gA, m12gB] gzWord * m12Rep2 *
    (evalCodes [m12gA, m12gB] gzWord)⁻¹ :=
  Certificates.certificate11004.2.1

theorem m12_gens_mem' : ∀ g ∈ [m12gA, m12gB], g ∈ NativeSporadic.M12 := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact m12a.2
  · exact m12b.2

theorem card_centralizerIn_permZ : Nat.card (centralizerIn NativeSporadic.M12 permZ) = 240 := by
  rw [gz_conj, ← Nat.card_congr (centralizerInConjEquiv NativeSporadic.M12
    (evalCodes_mem _ m12_gens_mem' gzWord) m12Rep2).toEquiv, card_centralizerIn_m12Rep2]

theorem fourClassesLarge_of_check {Q : RawSchreierDatum 24} (hQ : ValidSchreier Q)
    {gs reps : List (Equiv.Perm (Fin 24))}
    (hgs : Q.originalSubgroup = Subgroup.closure {g | g ∈ gs})
    (hreps : ∀ r ∈ reps, ∃ w, r = evalCodes gs w)
    (hok : repsOK 24 (listTables gs) (listTables (gs.map (·⁻¹))) (cosetOrderTables Q 1 4)
      (reps.map toTable) 1000 = true)
    (hsz : (repSizes 24 (listTables gs) (listTables (gs.map (·⁻¹))) (reps.map toTable)
      1000).all (fun k => decide (5 ≤ k)) = true)
    (hord : (reps.map toTable).all (ordTest 24 4) = true) :
    FourClassesLarge Q.originalSubgroup := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  have hgs' : ∀ g ∈ gs, g ∈ Q.originalSubgroup := fun g hg => by
    rw [hgs]
    exact Subgroup.subset_closure hg
  refine fourClassesLarge_of_repsOK hn Q hQ gs hgs' reps (fun r hr => ⟨?_, ?_⟩) 1000 hok
    fun r hr => ?_
  · obtain ⟨w, rfl⟩ := hreps r hr
    exact evalCodes_mem _ hgs' w
  · exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
      (List.all_eq_true.1 hord _ (List.mem_map_of_mem hr))
  · exact of_decide_eq_true (List.all_eq_true.1 hsz _
      (List.mem_map_of_mem (List.mem_map_of_mem hr)))

theorem q2Q_spec : q2Q.originalSubgroup = centralizerIn autModel m12A1 ∧
    Nat.card q2Q.originalSubgroup = 384 ∧ FourClassesLarge q2Q.originalSubgroup := by
  have h := checkQ2_eq
  simp only [checkQ2, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hc, ho⟩, hcomm⟩, hok⟩, hsz⟩, hord⟩ := h
  have hcard : Nat.card q2Q.originalSubgroup = 384 := by
    rw [← q2Q.orderCertificate_eq_card hc, ho]
  have hle : q2Q.originalSubgroup ≤ centralizerIn autModel m12A1 := by
    rw [q2Q, certificate_originalSubgroup]
    exact closure_le_centralizerIn (by norm_num) (modelGens_mem _) hcomm
  refine ⟨Subgroup.eq_of_le_of_card_ge hle ?_, hcard, fourClassesLarge_of_check hc
    (by rw [q2Q, certificate_originalSubgroup]) (fun r hr => ?_) hok hsz hord⟩
  · have := card_centralizerIn_autModel_le m12a
    rw [m12EquivD_m12a, show ((m12a : NativeSporadic.M12) : Equiv.Perm (Fin 12)) = m12Rep1 from
      m12Rep1_eq.symm, card_centralizerIn_m12Rep1] at this
    rw [hcard]
    exact this
  · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
    exact ⟨w, rfl⟩

theorem q4Q_spec : q4Q.originalSubgroup = centralizerIn autModel (blockHom (permZ, permZ)) ∧
    Nat.card q4Q.originalSubgroup = 480 ∧ FourClassesLarge q4Q.originalSubgroup := by
  have h := checkQ4_eq
  simp only [checkQ4, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hc, ho⟩, hcomm⟩, hok⟩, hsz⟩, hord⟩ := h
  have hcard : Nat.card q4Q.originalSubgroup = 480 := by
    rw [← q4Q.orderCertificate_eq_card hc, ho]
  have hgens : ∀ g ∈ q4Gens, g ∈ autModel := by
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
      exact evalCodes_mem _ autModel_gens_mem _
    · rw [List.mem_singleton.1 hg]
      exact sigma_mem_autModel
  have hle : q4Q.originalSubgroup ≤ centralizerIn autModel (blockHom (permZ, permZ)) := by
    rw [q4Q, certificate_originalSubgroup]
    exact closure_le_centralizerIn (by norm_num) hgens hcomm
  refine ⟨Subgroup.eq_of_le_of_card_ge hle ?_, hcard, fourClassesLarge_of_check hc
    (by rw [q4Q, certificate_originalSubgroup]) (fun r hr => ?_) hok hsz hord⟩
  · have := card_centralizerIn_autModel_le elemZ
    rw [m12EquivD_elemZ, elemZ_coe, card_centralizerIn_permZ] at this
    rw [hcard]
    exact this
  · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
    exact ⟨w, rfl⟩

theorem q5Q_spec : q5Q.originalSubgroup = centralizerIn autModel m12Sigma ∧
    Nat.card q5Q.originalSubgroup = 240 ∧ FourClassesLarge q5Q.originalSubgroup := by
  have h := checkQ5_eq
  simp only [checkQ5, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hc, ho⟩, hcomm⟩, hok⟩ := h
  have hcard : Nat.card q5Q.originalSubgroup = 240 := by
    rw [← q5Q.orderCertificate_eq_card hc, ho]
  have hle : q5Q.originalSubgroup ≤ centralizerIn autModel m12Sigma := by
    rw [q5Q, certificate_originalSubgroup]
    exact closure_le_centralizerIn (by norm_num) (modelGens_mem _) hcomm
  refine ⟨Subgroup.eq_of_le_of_card_ge hle ?_, hcard, fourClassesLarge_of_check (reps := []) hc
    (by rw [q5Q, certificate_originalSubgroup]) (by simp) (by simpa using hok)
    (by simp [repSizes]) (by simp)⟩
  have := card_le_two_mul_inf (centralizerIn autModel m12Sigma) inf_le_left
  rw [centralizerIn_autModel_inf, centralizerIn_blockGroup_sigma,
    ← m12SigmaCentQ.orderCertificate_eq_card m12_sigma_cent.1, m12_sigma_cent.2.1] at this
  rw [hcard]
  exact this

@[expose] def elemRep2 : NativeSporadic.M12 := ⟨m12Rep2, (m12_reps_mem _ (by simp)).1⟩

@[expose] def elemGz : NativeSporadic.M12 :=
  ⟨evalCodes [m12gA, m12gB] gzWord, evalCodes_mem _ m12_gens_mem' gzWord⟩

theorem elemZ_eq_conj : elemZ = elemGz * elemRep2 * elemGz⁻¹ := Subtype.ext gz_conj

theorem fourClassesLarge_m12 {v : Equiv.Perm (Fin 12)} (hv : v ∈ NativeSporadic.M12)
    (h2 : orderOf v = 2) : FourClassesLarge (centralizerIn NativeSporadic.M12 v) := by
  obtain ⟨r, hr, c, hc, rfl⟩ := m12_involution_cover.1 v (by rw [inv_one, one_mul]; exact hv) h2
  refine FourClassesLarge.of_mulEquiv (centralizerInConjEquiv NativeSporadic.M12 hc r).symm ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact fourClassesLarge_m12Rep1
  · exact fourClassesLarge_m12Rep2

theorem autModel_involution_cover {δ : Equiv.Perm (Fin 24)} (hδ : δ ∈ autModel)
    (h2 : orderOf δ = 2) :
    ∃ r ∈ [m12A1, blockHom (permZ, permZ), m12Sigma], ∃ c ∈ autModel, δ = c * r * c⁻¹ := by
  rcases hδ with hD | hσ
  · set v : NativeSporadic.M12 := m12EquivD.symm ⟨δ, hD⟩ with hvdef
    have hv2 : orderOf (v : Equiv.Perm (Fin 12)) = 2 := by
      rw [Subgroup.orderOf_coe, hvdef, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, h2]
    obtain ⟨r, hr, c, hc, hvc⟩ :=
      m12_involution_cover.1 _ (by rw [inv_one, one_mul]; exact v.2) hv2
    have hδv : δ = (m12EquivD v : Equiv.Perm (Fin 24)) := by simp [hvdef]
    have hrM : r ∈ NativeSporadic.M12 := (m12_reps_mem r hr).1
    have hv' : v = ⟨c, hc⟩ * ⟨r, hrM⟩ * (⟨c, hc⟩ : NativeSporadic.M12)⁻¹ := Subtype.ext hvc
    have hcm : ((m12EquivD ⟨c, hc⟩ : blockGroup) : Equiv.Perm (Fin 24)) ∈ autModel :=
      blockGroup_le_autModel (m12EquivD ⟨c, hc⟩).2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have hr' : (⟨m12Rep1, hrM⟩ : NativeSporadic.M12) = m12a := Subtype.ext m12Rep1_eq
      refine ⟨m12A1, by simp, _, hcm, ?_⟩
      rw [hδv, hv', hr', map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, m12EquivD_m12a]
    · have hr0 : elemGz⁻¹ * elemZ * elemGz = elemRep2 := by
        rw [elemZ_eq_conj]
        group
      have hr' : (⟨m12Rep2, hrM⟩ : NativeSporadic.M12) = elemGz⁻¹ * elemZ * elemGz := by
        rw [hr0]
        rfl
      have hgm : ((m12EquivD elemGz : blockGroup) : Equiv.Perm (Fin 24)) ∈ autModel :=
        blockGroup_le_autModel (m12EquivD elemGz).2
      refine ⟨blockHom (permZ, permZ), by simp, _,
        autModel.mul_mem hcm (autModel.inv_mem hgm), ?_⟩
      rw [hδv, hv', hr']
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, m12EquivD_elemZ]
      group
  · have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
    obtain ⟨hok, -, hord⟩ := m12_sigma_cover
    have hA : m12A1 ∈ m12D.originalSubgroup := m12_gens_memD _ (by simp)
    have hB : m12B1 ∈ m12D.originalSubgroup := m12_gens_memD _ (by simp)
    have hord' : orderOf m12Sigma = 2 :=
      (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hord
    obtain ⟨hcov, -⟩ := exists_conj_of_repsOK hn m12D m12D_check.1 (pairTables_spec hn hA hB)
      m12Sigma (inv_conj_mem _ m12D_sigma_normalizes m12D_sigma_sq) (by norm_num) [m12Sigma]
      (fun r hr => by
        rw [List.mem_singleton] at hr
        subst hr
        exact ⟨by simp, hord'⟩) 1000 hok
    obtain ⟨r, hr, c, hc, rfl⟩ := hcov δ (by rw [sigma_inv]; exact hσ) h2
    rw [List.mem_singleton] at hr
    subst hr
    exact ⟨m12Sigma, by simp, c, blockGroup_le_autModel hc, rfl⟩

theorem fourClassesLarge_autModel {δ : Equiv.Perm (Fin 24)} (hδ : δ ∈ autModel)
    (h2 : orderOf δ = 2) : FourClassesLarge (centralizerIn autModel δ) := by
  obtain ⟨r, hr, c, hc, rfl⟩ := autModel_involution_cover hδ h2
  refine FourClassesLarge.of_mulEquiv (centralizerInConjEquiv autModel hc r).symm ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [← q2Q_spec.1]
    exact q2Q_spec.2.2
  · rw [← q4Q_spec.1]
    exact q4Q_spec.2.2
  · rw [← q5Q_spec.1]
    exact q5Q_spec.2.2

theorem index_inner : (inner NativeSporadic.M12).index = 2 := by
  have h := (inner NativeSporadic.M12).card_mul_index
  rw [card_inner, card_mulAut] at h
  omega

theorem eq_inner_or_top {J : Subgroup (MulAut NativeSporadic.M12)}
    (hJ : inner NativeSporadic.M12 ≤ J) : J = inner NativeSporadic.M12 ∨ J = ⊤ := by
  have h := Subgroup.relIndex_mul_index hJ
  rw [index_inner] at h
  have hJi : J.index ∣ 2 := Dvd.intro_left _ h
  rcases (Nat.dvd_prime Nat.prime_two).1 hJi with h1 | h1
  · exact Or.inr (Subgroup.index_eq_one.1 h1)
  · left
    rw [h1] at h
    have : (inner NativeSporadic.M12).relIndex J = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.1 this) hJ

@[expose] noncomputable def innerEquiv : NativeSporadic.M12 ≃* inner NativeSporadic.M12 :=
  MonoidHom.ofInjective conj_injective

theorem centralizerIn_top {G : Type*} [Group G] (t : G) :
    centralizerIn (⊤ : Subgroup G) t = Subgroup.centralizer {t} :=
  top_inf_eq _

theorem fourClassesLarge_centralizer (J : Subgroup (MulAut NativeSporadic.M12))
    (hJ : inner NativeSporadic.M12 ≤ J) (u : J) (hu : orderOf u = 2) :
    FourClassesLarge (Subgroup.centralizer ({u} : Set J)) := by
  rcases eq_inner_or_top hJ with rfl | rfl
  · refine FourClassesLarge.of_mulEquiv (centralizerEquiv innerEquiv.symm u) ?_
    refine FourClassesLarge.of_mulEquiv
      (centralizerSubgroupEquiv NativeSporadic.M12 (innerEquiv.symm u)) ?_
    apply fourClassesLarge_m12 (innerEquiv.symm u).2
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hu]
  · refine FourClassesLarge.of_mulEquiv (centralizerSubgroupEquiv ⊤ u) ?_
    rw [centralizerIn_top]
    refine FourClassesLarge.of_mulEquiv
      (centralizerEquiv autModelEquiv.symm (u : MulAut NativeSporadic.M12)) ?_
    refine FourClassesLarge.of_mulEquiv
      (centralizerSubgroupEquiv autModel (autModelEquiv.symm u)) ?_
    apply fourClassesLarge_autModel (autModelEquiv.symm u).2
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hu]

theorem centralizer_inner_subgroupOf (J : Subgroup (MulAut NativeSporadic.M12))
    (hJ : inner NativeSporadic.M12 ≤ J) :
    Subgroup.centralizer (((inner NativeSporadic.M12).subgroupOf J : Subgroup J) : Set J) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_centralizer_iff] at hx
  have hfix : ∀ g : NativeSporadic.M12, (x : MulAut NativeSporadic.M12) g = g := by
    intro g
    have h1 := hx ⟨MulAut.conj g, hJ ⟨g, rfl⟩⟩
      (by rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact ⟨g, rfl⟩)
    have h2 : MulAut.conj g * (x : MulAut NativeSporadic.M12) =
        (x : MulAut NativeSporadic.M12) * MulAut.conj g := congrArg Subtype.val h1
    have h3 : MulAut.conj ((x : MulAut NativeSporadic.M12) g) = MulAut.conj g := by
      rw [conj_apply_eq, ← h2, mul_inv_cancel_right]
    exact conj_injective h3
  exact Subgroup.mem_bot.2 (Subtype.ext (MulEquiv.ext hfix))

theorem oddCore_centralizer (J : Subgroup (MulAut NativeSporadic.M12))
    (hJ : inner NativeSporadic.M12 ≤ J) (u : J) (hu : orderOf u = 2) :
    CFSG.oddCore (Subgroup.centralizer ({u} : Set J)) = ⊥ :=
  oddCore_centralizer_eq_bot_of_normal m12_inner_oddCore m12_mulAut_card m12_outer_oddCore
    ((inner NativeSporadic.M12).subgroupOf J)
    ((Subgroup.subgroupOfEquivOfLe hJ).trans innerEquiv.symm) (centralizer_inner_subgroupOf J hJ)
    u hu

theorem permA0_conj : permA0 = permG0 * m12gA * permG0⁻¹ :=
  Certificates.certificate11004.2.2.1

theorem permA1_conj : permA1 = permG1 * permZ * permG1⁻¹ :=
  Certificates.certificate11004.2.2.2.1

theorem permA0_apply : ∀ i, permA0 i = ![0, 1, 11, 4, 3, 5, 6, 10, 9, 8, 7, 2] i :=
  Certificates.certificate11004.2.2.2.2.1

theorem permA1_apply : ∀ i, permA1 i = ![1, 0, 3, 2, 11, 6, 5, 8, 7, 10, 9, 4] i :=
  Certificates.certificate11004.2.2.2.2.2

@[expose] def elemG0 : NativeSporadic.M12 := ⟨permG0, evalCodes_mem _ m12_gens_mem' g0Word⟩

@[expose] def elemG1 : NativeSporadic.M12 := ⟨permG1, evalCodes_mem _ m12_gens_mem' g1Word⟩

@[expose] def elemA0 : NativeSporadic.M12 := ⟨permA0, by
  rw [permA0_conj]
  exact mul_mem (mul_mem elemG0.2 m12a.2) (inv_mem elemG0.2)⟩

@[expose] def elemA1 : NativeSporadic.M12 := ⟨permA1, by
  rw [permA1_conj]
  exact mul_mem (mul_mem elemG1.2 elemZ.2) (inv_mem elemG1.2)⟩

theorem elemA0_eq : elemA0 = elemG0 * m12a * elemG0⁻¹ := Subtype.ext permA0_conj

theorem elemA1_eq : elemA1 = elemG1 * elemZ * elemG1⁻¹ := Subtype.ext permA1_conj

theorem orderOf_m12a : orderOf m12a = 2 := by
  rw [← Subgroup.orderOf_coe]
  change orderOf m12gA = 2
  rw [← m12Rep1_eq]
  exact (m12_reps_mem _ (by simp)).2

theorem orderOf_elemA0 : orderOf elemA0 = 2 := by
  rw [elemA0_eq, ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_m12a]

theorem orderOf_elemA1 : orderOf elemA1 = 2 := by
  rw [elemA1_eq, ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_elemZ]

theorem card_centralizer_elemA0 :
    Nat.card (Subgroup.centralizer ({elemA0} : Set NativeSporadic.M12)) = 192 := by
  rw [card_centralizer_eq_centralizerIn NativeSporadic.M12 elemA0]
  change Nat.card (centralizerIn NativeSporadic.M12 permA0) = 192
  rw [permA0_conj, ← Nat.card_congr (centralizerInConjEquiv NativeSporadic.M12
    (show permG0 ∈ NativeSporadic.M12 from elemG0.2) m12gA).toEquiv, ← m12Rep1_eq,
    card_centralizerIn_m12Rep1]

theorem card_centralizer_elemA1 :
    Nat.card (Subgroup.centralizer ({elemA1} : Set NativeSporadic.M12)) = 240 := by
  rw [card_centralizer_eq_centralizerIn NativeSporadic.M12 elemA1]
  change Nat.card (centralizerIn NativeSporadic.M12 permA1) = 240
  rw [permA1_conj, ← Nat.card_congr (centralizerInConjEquiv NativeSporadic.M12
    (show permG1 ∈ NativeSporadic.M12 from elemG1.2) permZ).toEquiv, card_centralizerIn_permZ]

theorem card_centralizer_mulAut (α : MulAut NativeSporadic.M12) :
    Nat.card (Subgroup.centralizer ({α} : Set (MulAut NativeSporadic.M12))) =
      Nat.card (centralizerIn autModel (autModelEquiv.symm α : Equiv.Perm (Fin 24))) := by
  rw [Nat.card_congr (centralizerEquiv autModelEquiv.symm α).toEquiv,
    card_centralizer_eq_centralizerIn]

theorem card_centralizer_conj_elemA0 : Nat.card (Subgroup.centralizer
    ({MulAut.conj elemA0} : Set (MulAut NativeSporadic.M12))) = 384 := by
  rw [card_centralizer_mulAut, autModelEquiv_symm_conj, autModelIota_coe, elemA0_eq, map_mul,
    map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, m12EquivD_m12a,
    ← Nat.card_congr (centralizerInConjEquiv autModel
      (blockGroup_le_autModel (m12EquivD elemG0).2) m12A1).toEquiv, ← q2Q_spec.1, q2Q_spec.2.1]

theorem card_centralizer_conj_elemA1 : Nat.card (Subgroup.centralizer
    ({MulAut.conj elemA1} : Set (MulAut NativeSporadic.M12))) = 480 := by
  rw [card_centralizer_mulAut, autModelEquiv_symm_conj, autModelIota_coe, elemA1_eq, map_mul,
    map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, m12EquivD_elemZ,
    ← Nat.card_congr (centralizerInConjEquiv autModel
      (blockGroup_le_autModel (m12EquivD elemG1).2) (blockHom (permZ, permZ))).toEquiv,
    ← q4Q_spec.1, q4Q_spec.2.1]

theorem card_centralizer_beta :
    Nat.card (Subgroup.centralizer ({beta} : Set (MulAut NativeSporadic.M12))) = 240 := by
  rw [card_centralizer_mulAut, autModelEquiv_symm_beta, sigmaModel_coe, ← q5Q_spec.1,
    q5Q_spec.2.1]

theorem m12_involution_conj_a0_a1 (v : NativeSporadic.M12) (hv : orderOf v = 2) :
    ∃ c : NativeSporadic.M12, v = c * elemA0 * c⁻¹ ∨ v = c * elemA1 * c⁻¹ := by
  obtain ⟨r, hr, c, hc, hvc⟩ := m12_involution_cover.1 (v : Equiv.Perm (Fin 12))
    (by rw [inv_one, one_mul]; exact v.2) (by rw [Subgroup.orderOf_coe, hv])
  have hv' : v = ⟨c, hc⟩ * ⟨r, (m12_reps_mem r hr).1⟩ * (⟨c, hc⟩ : NativeSporadic.M12)⁻¹ :=
    Subtype.ext hvc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have hr' : (⟨m12Rep1, (m12_reps_mem _ (by simp)).1⟩ : NativeSporadic.M12) =
        elemG0⁻¹ * elemA0 * elemG0 := by
      rw [elemA0_eq, show m12a = ⟨m12Rep1, (m12_reps_mem _ (by simp)).1⟩ from
        Subtype.ext m12Rep1_eq.symm]
      group
    refine ⟨⟨c, hc⟩ * elemG0⁻¹, Or.inl ?_⟩
    rw [hv', hr']
    group
  · have hr0 : (elemG1 * elemGz)⁻¹ * elemA1 * (elemG1 * elemGz) = elemRep2 := by
      rw [elemA1_eq, elemZ_eq_conj]
      group
    have hr' : (⟨m12Rep2, (m12_reps_mem _ (by simp)).1⟩ : NativeSporadic.M12) =
        (elemG1 * elemGz)⁻¹ * elemA1 * (elemG1 * elemGz) := by
      rw [hr0]
      rfl
    refine ⟨⟨c, hc⟩ * (elemG1 * elemGz)⁻¹, Or.inr ?_⟩
    rw [hv', hr']
    group

theorem ctss_m12_automorphism_involution_centralizers_exclude_small_normal_four_groups :
    (∀ J : Subgroup (MulAut NativeSporadic.M12), inner NativeSporadic.M12 ≤ J →
      J = inner NativeSporadic.M12 ∨ J = ⊤) ∧
    (∀ J : Subgroup (MulAut NativeSporadic.M12), inner NativeSporadic.M12 ≤ J →
      ∀ u : J, orderOf u = 2 →
        CFSG.oddCore (Subgroup.centralizer ({u} : Set J)) = ⊥ ∧
        ∀ N : Subgroup (Subgroup.centralizer ({u} : Set J)), N.Normal →
          IsEmpty (N ≃* Multiplicative (ZMod 4)) ∧
          IsEmpty (N ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4))) ∧
    (∀ i, permA0 i = ![0, 1, 11, 4, 3, 5, 6, 10, 9, 8, 7, 2] i) ∧
    (∀ i, permA1 i = ![1, 0, 3, 2, 11, 6, 5, 8, 7, 10, 9, 4] i) ∧
    orderOf elemA0 = 2 ∧ orderOf elemA1 = 2 ∧
    (∀ v : NativeSporadic.M12, orderOf v = 2 →
      ∃ c : NativeSporadic.M12, v = c * elemA0 * c⁻¹ ∨ v = c * elemA1 * c⁻¹) ∧
    Nat.card (Subgroup.centralizer ({elemA0} : Set NativeSporadic.M12)) = 192 ∧
    Nat.card (Subgroup.centralizer ({elemA1} : Set NativeSporadic.M12)) = 240 ∧
    Nat.card (Subgroup.centralizer
      ({MulAut.conj elemA0} : Set (MulAut NativeSporadic.M12))) = 384 ∧
    Nat.card (Subgroup.centralizer
      ({MulAut.conj elemA1} : Set (MulAut NativeSporadic.M12))) = 480 ∧
    Nat.card (Subgroup.centralizer ({beta} : Set (MulAut NativeSporadic.M12))) = 240 :=
  ⟨fun _ hJ => eq_inner_or_top hJ, fun J hJ u hu => ⟨oddCore_centralizer J hJ u hu,
      (fourClassesLarge_centralizer J hJ u hu).noNormalFour⟩,
    permA0_apply, permA1_apply, orderOf_elemA0, orderOf_elemA1, m12_involution_conj_a0_a1,
    card_centralizer_elemA0, card_centralizer_elemA1, card_centralizer_conj_elemA0,
    card_centralizer_conj_elemA1, card_centralizer_beta⟩

end CFSG.ComponentClassification.M12Cover
