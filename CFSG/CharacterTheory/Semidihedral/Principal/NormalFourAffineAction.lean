module

public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionSymmetricFour

public section

namespace CFSG.Semidihedral.Principal

universe u

namespace NormalFourAffine

open scoped Classical

variable {G : Type u} [Group G] [Fintype G] (V : Subgroup G) [V.Normal] [IsKleinFour V]

omit [Fintype G] [V.Normal] in
theorem exists_conj_ne (hmin : ∀ N : Subgroup G, N.Normal → N ≤ V → N = ⊥ ∨ N = V) {v : G}
    (hv : v ∈ V) (hv1 : v ≠ 1) : ∃ g : G, g * v * g⁻¹ ≠ v := by
  by_contra! hall
  have hnormal : (Subgroup.zpowers v).Normal := by
    constructor
    intro x hx g
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow, hall g]
    exact Subgroup.zpow_mem_zpowers v k
  have hle : Subgroup.zpowers v ≤ V := (Subgroup.zpowers_le).mpr hv
  rcases hmin _ hnormal hle with h | h
  · exact hv1 (Subgroup.zpowers_eq_bot.mp h)
  · have hv2 : orderOf v = 2 := by
      apply orderOf_eq_prime _ hv1
      have h1 := IsKleinFour.mul_self (⟨v, hv⟩ : V)
      rw [pow_two]
      exact congrArg Subtype.val h1
    have h1 := congrArg (fun H : Subgroup G => Nat.card H) h
    simp only [Nat.card_zpowers, hv2, IsKleinFour.card_four] at h1
    omega

omit [V.Normal] in
theorem card_erase_one : ((Finset.univ : Finset V).erase 1).card = 3 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, IsKleinFour.card_four']

omit [Fintype G] [IsKleinFour V] in
theorem conj_mem_ne (g : G) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    g * v * g⁻¹ ∈ V ∧ g * v * g⁻¹ ≠ 1 := by
  refine ⟨Subgroup.Normal.conj_mem inferInstance v hv g, fun h => hv1 ?_⟩
  calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
    _ = 1 := by rw [h]; group

theorem isConj_of_mem (hmin : ∀ N : Subgroup G, N.Normal → N ≤ V → N = ⊥ ∨ N = V) {v w : G}
    (hv : v ∈ V) (hw : w ∈ V) (hv1 : v ≠ 1) (hw1 : w ≠ 1) : IsConj v w := by
  by_contra hvw
  have hsub : ∀ u : G, u ∈ V → u ≠ 1 →
      (Finset.univ.filter (fun z : V => IsConj u (z : G))) ⊆ (Finset.univ : Finset V).erase 1 := by
    intro u hu hu1 z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨c, hc⟩ := isConj_iff.mp hz.2
    refine Finset.mem_erase.mpr ⟨fun h => ?_, Finset.mem_univ _⟩
    have h1 : (z : G) = 1 := congrArg Subtype.val h
    rw [← hc] at h1
    exact (conj_mem_ne V c hu hu1).2 h1
  have hcard2 : ∀ u : G, u ∈ V → u ≠ 1 →
      2 ≤ (Finset.univ.filter (fun z : V => IsConj u (z : G))).card := by
    intro u hu hu1
    obtain ⟨g, hg⟩ := exists_conj_ne V hmin hu hu1
    have hmem := conj_mem_ne V g hu hu1
    have hsub2 : ({⟨u, hu⟩, ⟨g * u * g⁻¹, hmem.1⟩} : Finset V) ⊆
        Finset.univ.filter (fun z : V => IsConj u (z : G)) := by
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hz with rfl | rfl
      · exact IsConj.refl u
      · exact isConj_iff.mpr ⟨g, rfl⟩
    have hne : (⟨u, hu⟩ : V) ≠ ⟨g * u * g⁻¹, hmem.1⟩ := fun h =>
      hg (congrArg Subtype.val h).symm
    calc 2 = ({⟨u, hu⟩, ⟨g * u * g⁻¹, hmem.1⟩} : Finset V).card := (Finset.card_pair hne).symm
      _ ≤ _ := Finset.card_le_card hsub2
  have hdisj : Disjoint (Finset.univ.filter (fun z : V => IsConj v (z : G)))
      (Finset.univ.filter (fun z : V => IsConj w (z : G))) := by
    rw [Finset.disjoint_left]
    intro z hzv hzw
    rw [Finset.mem_filter] at hzv hzw
    exact hvw (hzv.2.trans hzw.2.symm)
  have h1 := Finset.card_union_of_disjoint hdisj
  have h2 := Finset.card_le_card (Finset.union_subset (hsub v hv hv1) (hsub w hw hw1))
  have h3 := hcard2 v hv hv1
  have h4 := hcard2 w hw hw1
  rw [card_erase_one] at h2
  omega

theorem card_conj (hmin : ∀ N : Subgroup G, N.Normal → N ≤ V → N = ⊥ ∨ N = V) {v : G}
    (hv : v ∈ V) (hv1 : v ≠ 1) : Nat.card {w : G // IsConj w v} = 3 := by
  have h1 : Nat.card {w : G // IsConj w v} = Nat.card {z : V // z ≠ 1} := by
    refine Nat.card_congr
      { toFun := fun w => ⟨⟨w.1, ?_⟩, ?_⟩
        invFun := fun z => ⟨z.1, isConj_of_mem V hmin z.1.2 hv
          (fun h => z.2 (Subtype.ext h)) hv1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · obtain ⟨c, hc⟩ := isConj_iff.mp w.2.symm
      rw [← hc]
      exact (conj_mem_ne V c hv hv1).1
    · intro h
      obtain ⟨c, hc⟩ := isConj_iff.mp w.2.symm
      have h2 : (w : G) = 1 := congrArg Subtype.val h
      rw [← hc] at h2
      exact (conj_mem_ne V c hv hv1).2 h2
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_ne', card_erase_one]

omit [IsKleinFour V] in
theorem card_dvd_twenty_four [IsKleinFour V] (hcent : Subgroup.centralizer (V : Set G) = V) :
    Nat.card G ∣ 24 := by
  let φ : G →* Equiv.Perm V := (MulAut.toPerm V).comp MulAut.conjNormal
  have hker : φ.ker = V := by
    ext g
    rw [MonoidHom.mem_ker]
    refine Iff.trans ?_ (by rw [hcent] : g ∈ Subgroup.centralizer (V : Set G) ↔ g ∈ V)
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h x hx
      have h1 := congrArg (fun f : Equiv.Perm V => ((f ⟨x, hx⟩ : V) : G)) h
      change g * x * g⁻¹ = x at h1
      calc x * g = g * x * g⁻¹ * g := by rw [h1]
        _ = g * x := by group
    · intro h
      refine Equiv.ext fun x => Subtype.ext ?_
      change g * (x : G) * g⁻¹ = x
      rw [← h x x.2, mul_inv_cancel_right]
  have hrange : φ.range ≤ MulAction.stabilizer (Equiv.Perm V) (1 : V) := by
    rintro _ ⟨g, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    exact map_one (MulAut.conjNormal g : MulAut V)
  have hstab : Nat.card (MulAction.stabilizer (Equiv.Perm V) (1 : V)) = 6 := by
    have h1 := (MulAction.stabilizer (Equiv.Perm V) (1 : V)).card_mul_index
    rw [MulAction.index_stabilizer_of_transitive (Equiv.Perm V) (1 : V), Nat.card_perm,
      IsKleinFour.card_four (G := V)] at h1
    rw [show (4 : ℕ).factorial = 24 from rfl] at h1
    omega
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [hker, IsKleinFour.card_four] at h1
  have h2 : Nat.card φ.range ∣ 6 := hstab ▸ Subgroup.card_dvd_of_le hrange
  rw [← h1]
  exact Nat.mul_dvd_mul_left 4 h2

omit [V.Normal] in
theorem exists_ne_one : ∃ v ∈ V, v ≠ 1 := by
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by rw [card_erase_one]; norm_num :
    0 < ((Finset.univ : Finset V).erase 1).card)
  exact ⟨z, z.2, fun h => (Finset.mem_erase.mp hz).1 (Subtype.ext h)⟩

theorem card_eq (hmin : ∀ N : Subgroup G, N.Normal → N ≤ V → N = ⊥ ∨ N = V)
    (hcent : Subgroup.centralizer (V : Set G) = V) : Nat.card G = 12 ∨ Nat.card G = 24 := by
  obtain ⟨v, hvV, hv1⟩ := exists_ne_one V
  have h3 : 3 ∣ Nat.card G := by
    rw [← CyclicSymmetricFour.card_centralizer_mul_card_conj v, card_conj V hmin hvV hv1]
    exact Dvd.intro_left _ rfl
  have h4 : 4 ∣ Nat.card G := by
    rw [← IsKleinFour.card_four (G := V)]
    exact Subgroup.card_subgroup_dvd_card V
  have h24 := card_dvd_twenty_four V hcent
  have hle := Nat.le_of_dvd (by norm_num) h24
  have hpos : 0 < Nat.card G := Nat.card_pos
  omega

theorem exists_complement (hmin : ∀ N : Subgroup G, N.Normal → N ≤ V → N = ⊥ ∨ N = V)
    (hcent : Subgroup.centralizer (V : Set G) = V) : ∃ N : Subgroup G, V ⊔ N = ⊤ ∧ V ⊓ N = ⊥ := by
  have hcard := card_eq V hmin hcent
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨T⟩ : Nonempty (Sylow 3 G) := inferInstance
  have hT3 : Nat.card (T : Subgroup G) = 3 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp T.isPGroup'
    have hidx := T.not_dvd_index
    have hmul := (T : Subgroup G).card_mul_index
    rw [hk] at hmul
    rcases k with _ | _ | k
    · exfalso
      rw [pow_zero, one_mul] at hmul
      apply hidx
      rw [hmul]
      rcases hcard with h | h <;> rw [h] <;> norm_num
    · rw [hk, pow_one]
    · exfalso
      have h9 : 9 ∣ Nat.card G := ⟨3 ^ k * (T : Subgroup G).index, by rw [← hmul]; ring⟩
      rcases hcard with h | h <;> rw [h] at h9 <;> norm_num at h9
  have hVT : V ⊓ (T : Subgroup G) = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard
    (by rw [IsKleinFour.card_four, hT3]; norm_num))
  have h12 : 12 ∣ Nat.card (V ⊔ (T : Subgroup G) : Subgroup G) := by
    have h4 : 4 ∣ Nat.card (V ⊔ (T : Subgroup G) : Subgroup G) := by
      rw [← IsKleinFour.card_four (G := V)]
      exact Subgroup.card_dvd_of_le le_sup_left
    have h3 : 3 ∣ Nat.card (V ⊔ (T : Subgroup G) : Subgroup G) := by
      have h5 := Subgroup.card_dvd_of_le (le_sup_right : (T : Subgroup G) ≤ V ⊔ (T : Subgroup G))
      rwa [hT3] at h5
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 3) h4 h3
  have hMn : (V ⊔ (T : Subgroup G)).Normal := by
    have hmul := (V ⊔ (T : Subgroup G)).card_mul_index
    obtain ⟨k, hk⟩ := h12
    rw [hk] at hmul
    have hidx : (V ⊔ (T : Subgroup G)).index = 1 ∨ (V ⊔ (T : Subgroup G)).index = 2 := by
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h] at hmul
          rcases hcard with h' | h' <;> rw [h'] at hmul <;> simp at hmul
        · exact h
      rcases hcard with h | h <;> rw [h] at hmul
      · left
        nlinarith
      · rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · interval_cases k
          right
          omega
        · left
          nlinarith
    rcases hidx with h | h
    · rw [Subgroup.index_eq_one.mp h]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h
  have hfr := Sylow.normalizer_sup_eq_top' (N := V ⊔ (T : Subgroup G)) T le_sup_right
  refine ⟨Subgroup.normalizer (T : Set G), ?_, ?_⟩
  · rw [eq_top_iff, ← hfr]
    exact sup_le le_sup_right (sup_le le_sup_left
      ((Subgroup.le_normalizer).trans le_sup_right))
  · rw [eq_bot_iff]
    intro v ⟨hvV, hvN⟩
    by_contra hv1
    have hv1' : v ≠ 1 := fun h => hv1 (Subgroup.mem_bot.mpr h)
    have hTC : (T : Subgroup G) ≤ Subgroup.centralizer {v} := by
      intro t ht
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : v * t * v⁻¹ * t⁻¹ ∈ V ⊓ (T : Subgroup G) := by
        refine ⟨?_, ?_⟩
        · have h2 : t * v⁻¹ * t⁻¹ ∈ V := Subgroup.Normal.conj_mem inferInstance _
            (Subgroup.inv_mem _ hvV) t
          have h3 : v * t * v⁻¹ * t⁻¹ = v * (t * v⁻¹ * t⁻¹) := by group
          rw [h3]
          exact Subgroup.mul_mem _ hvV h2
        · have h2 : v * t * v⁻¹ ∈ (T : Subgroup G) := (Subgroup.mem_normalizer_iff.mp hvN t).mp ht
          exact Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ ht)
      rw [hVT, Subgroup.mem_bot] at h1
      calc t * v = (v * t * v⁻¹ * t⁻¹)⁻¹ * (v * t) := by group
        _ = v * t := by rw [h1, inv_one, one_mul]
    have hVC : V ≤ Subgroup.centralizer {v} := by
      intro w hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := IsKleinFour.isMulCommutative.is_comm.comm (⟨w, hw⟩ : V) ⟨v, hvV⟩
      exact congrArg Subtype.val h1
    have h12' : 12 ∣ Nat.card (Subgroup.centralizer {v}) := by
      have h4 : 4 ∣ Nat.card (Subgroup.centralizer {v}) := by
        rw [← IsKleinFour.card_four (G := V)]
        exact Subgroup.card_dvd_of_le hVC
      have h3 : 3 ∣ Nat.card (Subgroup.centralizer {v}) := by
        have h5 := Subgroup.card_dvd_of_le hTC
        rwa [hT3] at h5
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 3) h4 h3
    have h3 := CyclicSymmetricFour.card_centralizer_mul_card_conj v
    rw [card_conj V hmin hvV hv1'] at h3
    have hpos : 0 < Nat.card (Subgroup.centralizer {v}) := Nat.card_pos
    obtain ⟨k, hk⟩ := h12'
    rcases hcard with h | h <;> rw [h, hk] at h3 <;> omega

end NormalFourAffine

open scoped Classical in
theorem normal_four_self_centralizing_affine_action {G : Type u} [Group G] [Fintype G]
    (V : Subgroup G) [V.Normal] [IsKleinFour V]
    (hmin : ∀ N : Subgroup G, N.Normal → N ≤ V → N = ⊥ ∨ N = V)
    (hcent : Subgroup.centralizer (V : Set G) = V) :
    ∃ ρ : G →* Equiv.Perm V, Function.Injective ρ ∧ (∀ v w : V, ρ v w = v * w) ∧
      alternatingGroup V ≤ ρ.range ∧
      (Nonempty (G ≃* alternatingGroup V) ∨ Nonempty (G ≃* Equiv.Perm V)) := by
  obtain ⟨N, hsup, hinf⟩ := NormalFourAffine.exists_complement V hmin hcent
  have hcard := NormalFourAffine.card_eq V hmin hcent
  let f : V → G ⧸ N := fun w => ((w : G) : G ⧸ N)
  have hf_inj : Function.Injective f := by
    intro w w' h
    have h1 : (w : G)⁻¹ * w' ∈ N := QuotientGroup.eq.mp h
    have h3 : (w : G)⁻¹ * w' ∈ V ⊓ N := ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ w.2) w'.2, h1⟩
    rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at h3
    exact Subtype.ext h3
  have hf_surj : Function.Surjective f := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg : g ∈ V ⊔ N := by
      rw [hsup]
      trivial
    rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hg
    obtain ⟨v, hv, n, hn, rfl⟩ := hg
    exact ⟨⟨v, hv⟩, QuotientGroup.eq.mpr (by simpa using hn)⟩
  let e : V ≃ G ⧸ N := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  let ρ : G →* Equiv.Perm V :=
    e.symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (G ⧸ N))
  have hρv : ∀ v w : V, ρ v w = v * w := by
    intro v w
    change e.symm ((v : G) • e w) = v * w
    rw [show (v : G) • e w = e (v * w) from rfl, Equiv.symm_apply_apply]
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    change e.symm.permCongrHom (MulAction.toPermHom G (G ⧸ N) g) = 1 at hg
    rw [MulEquiv.map_eq_one_iff] at hg
    have hcore : g ∈ N.normalCore := by
      rw [Subgroup.normalCore_eq_ker]
      exact hg
    have hcore_le : N.normalCore ≤ V := by
      intro k hk
      rw [← hcent, Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 : k * v * k⁻¹ * v⁻¹ ∈ V ⊓ N := by
        refine ⟨Subgroup.mul_mem _ (Subgroup.Normal.conj_mem inferInstance v hv k)
          (Subgroup.inv_mem _ hv), Subgroup.normalCore_le N ?_⟩
        have h2 : v * k⁻¹ * v⁻¹ ∈ N.normalCore :=
          Subgroup.Normal.conj_mem inferInstance _ (Subgroup.inv_mem _ hk) v
        have h3 : k * v * k⁻¹ * v⁻¹ = k * (v * k⁻¹ * v⁻¹) := by group
        rw [h3]
        exact Subgroup.mul_mem _ hk h2
      rw [hinf, Subgroup.mem_bot] at h1
      calc v * k = (k * v * k⁻¹ * v⁻¹)⁻¹ * (k * v) := by group
        _ = k * v := by rw [h1, inv_one, one_mul]
    have h1 : g ∈ V ⊓ N := ⟨hcore_le hcore, Subgroup.normalCore_le N hcore⟩
    rw [hinf] at h1
    exact h1
  have hrange : Nat.card ρ.range = Nat.card G := Nat.card_range_of_injective hinj
  have hperm : Nat.card (Equiv.Perm V) = 24 := by
    rw [Nat.card_perm, IsKleinFour.card_four]
    rfl
  have hidx := ρ.range.card_mul_index
  rw [hrange, hperm] at hidx
  have hle : ρ.range.index ≤ 2 := by
    rcases hcard with h | h <;> rw [h] at hidx <;> omega
  refine ⟨ρ, hinj, hρv, Equiv.Perm.alternatingGroup_le_of_index_le_two hle, ?_⟩
  rcases hcard with h | h
  · left
    have h2 : ρ.range.index = 2 := by
      rw [h] at hidx
      omega
    exact ⟨(MonoidHom.ofInjective hinj).trans
      (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two h2))⟩
  · right
    have htop : ρ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hrange, hperm, h])
    exact ⟨(MonoidHom.ofInjective hinj).trans
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)⟩

end CFSG.Semidihedral.Principal
