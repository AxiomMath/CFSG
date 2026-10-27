module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinJoins
public import CFSG.LocalAnalysis.ComponentClassification.PComponentNormalizerEnlargement
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG CFSG.LocalCores Subgroup
open scoped commutatorElement Pointwise

variable {H : Type*} [Group H]

theorem mem_conjugate_iff {K : Subgroup H} {g x : H} :
    x ∈ conjugate K g ↔ g * x * g⁻¹ ∈ K := by
  unfold conjugate
  rw [mem_map_equiv, MulAut.conj_symm_apply, inv_inv]

theorem conj_mem_conjugate {K : Subgroup H} {k : H} (hk : k ∈ K) (g : H) :
    g⁻¹ * k * g ∈ conjugate K g := by
  rw [mem_conjugate_iff, show g * (g⁻¹ * k * g) * g⁻¹ = k by group]
  exact hk

theorem conjugate_conjugate (K : Subgroup H) (a b : H) :
    conjugate (conjugate K a) b = conjugate K (a * b) := by
  ext x
  rw [mem_conjugate_iff, mem_conjugate_iff, mem_conjugate_iff,
    show a * (b * x * b⁻¹) * a⁻¹ = a * b * x * (a * b)⁻¹ by group]

theorem conjugate_one (K : Subgroup H) : conjugate K 1 = K := by
  ext x
  rw [mem_conjugate_iff, one_mul, inv_one, mul_one]

theorem conjugate_conjugate_inv (K : Subgroup H) (g : H) :
    conjugate (conjugate K g) g⁻¹ = K := by
  rw [conjugate_conjugate, mul_inv_cancel, conjugate_one]

theorem isComponent_conjugate {K : Subgroup H} (hK : IsComponent K) (g : H) :
    IsComponent (conjugate K g) := by
  unfold conjugate
  exact isComponent_map_mulEquiv _ hK

theorem isComponent_conjugate_iff (K : Subgroup H) (g : H) :
    IsComponent (conjugate K g) ↔ IsComponent K := by
  refine ⟨fun h => ?_, fun h => isComponent_conjugate h g⟩
  rw [← conjugate_conjugate_inv K g]
  exact isComponent_conjugate h g⁻¹

theorem mem_centralizer_singleton_iff_conj {c t : H} :
    c ∈ centralizer ({t} : Set H) ↔ t⁻¹ * c * t = c := by
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
  · intro h
    calc c * t = t * (t⁻¹ * c * t) := by group
      _ = t * c := by rw [h]

theorem sSup_le_layer {S : Set (Subgroup H)} (hS : ∀ N ∈ S, IsComponent N) :
    sSup S ≤ layer H :=
  sSup_le fun N hN => component_le_layer (hS N hN)

theorem mem_normalizer_sSup {S : Set (Subgroup H)} {g : H}
    (hg : ∀ N ∈ S, g ∈ normalizer (N : Set H)) :
    g ∈ normalizer ((sSup S : Subgroup H) : Set H) := by
  have key : ∀ g : H, (∀ N ∈ S, g ∈ normalizer (N : Set H)) →
      ∀ h ∈ sSup S, g * h * g⁻¹ ∈ sSup S := by
    intro g hg h hh
    have hle : sSup S ≤ (sSup S).comap (MulAut.conj g).toMonoidHom := by
      refine sSup_le fun N hN x hx => ?_
      rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact le_sSup hN ((mem_normalizer_iff.mp (hg N hN) x).mp hx)
    have h1 := mem_comap.mp (hle hh)
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  rw [mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun hh => ?_⟩
  have h1 := key g⁻¹ (fun N hN => inv_mem (hg N hN)) _ hh
  rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at h1

theorem conj_mem_sSup {S : Set (Subgroup H)} {t : H} (hS : ∀ N ∈ S, conjugate N t ∈ S)
    {a : H} (ha : a ∈ sSup S) : t⁻¹ * a * t ∈ sSup S := by
  have hle : sSup S ≤ (sSup S).comap (MulAut.conj t⁻¹).toMonoidHom := by
    refine sSup_le fun N hN x hx => ?_
    rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact le_sSup (hS N hN) (conj_mem_conjugate hx t)
  have h1 := mem_comap.mp (hle ha)
  rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1

variable [Finite H]

theorem sSup_isSubnormal {S : Set (Subgroup H)} (hS : ∀ N ∈ S, IsComponent N) :
    (sSup S).IsSubnormal := by
  have : (layer H).Characteristic := layer_characteristic
  have hE : (layer H).Normal := inferInstance
  refine IsSubnormal.step _ (layer H) (sSup_le_layer hS) hE.isSubnormal ?_
  rw [normal_subgroupOf_iff_le_normalizer (sSup_le_layer hS)]
  intro g hg
  exact mem_normalizer_sSup fun N hN => layer_le_normalizer (hS N hN) hg

theorem sSup_le_centralizer_sSup {S S' : Set (Subgroup H)} (hS : ∀ N ∈ S, IsComponent N)
    (hS' : ∀ N ∈ S', IsComponent N) (hdisj : ∀ N ∈ S, N ∉ S') :
    sSup S ≤ centralizer ((sSup S' : Subgroup H) : Set H) := by
  refine sSup_le fun N hN => ?_
  rw [le_centralizer_iff]
  refine sSup_le fun N' hN' => ?_
  rcases distinct_components_commute (hS' N' hN') (hS N hN) with h | h
  · exact absurd (h ▸ hN') (hdisj N hN)
  · exact commutator_eq_bot_iff_le_centralizer.mp h

omit [Finite H]

theorem commutatorElement_mul_mul_of_commute {g h c d : H} (hch : Commute c h)
    (hdg : Commute d g) (hcd : Commute c d) : ⁅g * c, h * d⁆ = ⁅g, h⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc g * c * (h * d) * (g * c)⁻¹ * (h * d)⁻¹
      = g * (c * h) * d * c⁻¹ * g⁻¹ * d⁻¹ * h⁻¹ := by group
    _ = g * (h * c) * d * c⁻¹ * g⁻¹ * d⁻¹ * h⁻¹ := by rw [hch.eq]
    _ = g * h * (c * d) * c⁻¹ * g⁻¹ * d⁻¹ * h⁻¹ := by group
    _ = g * h * (d * c) * c⁻¹ * g⁻¹ * d⁻¹ * h⁻¹ := by rw [hcd.eq]
    _ = g * h * (d * g⁻¹) * d⁻¹ * h⁻¹ := by group
    _ = g * h * (g⁻¹ * d) * d⁻¹ * h⁻¹ := by rw [hdg.inv_right.eq]
    _ = g * h * g⁻¹ * h⁻¹ := by group

theorem commutatorElement_mul_mul_eq_mul {a a' b b' : H} (h1 : Commute a b)
    (h2 : Commute a b') (h3 : Commute a' b) (h4 : Commute a' b') :
    ⁅a * b, a' * b'⁆ = ⁅a, a'⁆ * ⁅b, b'⁆ := by
  have hP : Commute (b * b' * b⁻¹) a⁻¹ :=
    ((h1.symm.mul_left h2.symm).mul_left h1.symm.inv_left).inv_right
  have hY : Commute (b * b' * b⁻¹ * b'⁻¹) a'⁻¹ :=
    (((h3.symm.mul_left h4.symm).mul_left h3.symm.inv_left).mul_left h4.symm.inv_left).inv_right
  rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
  calc a * b * (a' * b') * (a * b)⁻¹ * (a' * b')⁻¹
      = a * (b * a') * b' * b⁻¹ * a⁻¹ * b'⁻¹ * a'⁻¹ := by group
    _ = a * (a' * b) * b' * b⁻¹ * a⁻¹ * b'⁻¹ * a'⁻¹ := by rw [← h3.eq]
    _ = a * a' * (b * b' * b⁻¹ * a⁻¹) * b'⁻¹ * a'⁻¹ := by group
    _ = a * a' * (a⁻¹ * (b * b' * b⁻¹)) * b'⁻¹ * a'⁻¹ := by rw [hP.eq]
    _ = a * a' * a⁻¹ * (b * b' * b⁻¹ * b'⁻¹ * a'⁻¹) := by group
    _ = a * a' * a⁻¹ * (a'⁻¹ * (b * b' * b⁻¹ * b'⁻¹)) := by rw [hY.eq]
    _ = a * a' * a⁻¹ * a'⁻¹ * (b * b' * b⁻¹ * b'⁻¹) := by group

theorem conj_commutatorElement (t a b : H) :
    t⁻¹ * ⁅a, b⁆ * t = ⁅t⁻¹ * a * t, t⁻¹ * b * t⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutator_centralizer_sup_le {A B : Subgroup H} {t : H}
    (hA : ∀ a ∈ A, t⁻¹ * a * t ∈ A) (hB : ∀ b ∈ B, t⁻¹ * b * t ∈ B)
    (hAB : A ≤ centralizer (B : Set H)) :
    ⁅(A ⊔ B) ⊓ centralizer ({t} : Set H), (A ⊔ B) ⊓ centralizer ({t} : Set H)⁆ ≤
      A ⊓ centralizer ({t} : Set H) ⊔ B ⊓ centralizer ({t} : Set H) := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b := fun a ha b hb =>
    (mem_centralizer_iff.mp (hAB ha) b hb).symm
  have hsup : ((A ⊔ B : Subgroup H) : Set H) = (A : Set H) * (B : Set H) :=
    coe_mul_of_left_le_normalizer_right A B (hAB.trans (centralizer_le_normalizer _))
  have hdisp : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ centralizer ({t} : Set H) →
      a⁻¹ * (t⁻¹ * a * t) ∈ A ⊓ B ∧ b⁻¹ * (t⁻¹ * b * t) ∈ A ⊓ B := by
    intro a ha b hb hx
    have ha1 := hA a ha
    have hb1 := hB b hb
    have hfix : (t⁻¹ * a * t) * (t⁻¹ * b * t) = a * b := by
      rw [← mem_centralizer_singleton_iff_conj.mp hx]
      group
    have hz : a⁻¹ * (t⁻¹ * a * t) = b * (t⁻¹ * b * t)⁻¹ := by
      calc a⁻¹ * (t⁻¹ * a * t)
          = a⁻¹ * ((t⁻¹ * a * t) * (t⁻¹ * b * t)) * (t⁻¹ * b * t)⁻¹ := by group
        _ = b * (t⁻¹ * b * t)⁻¹ := by rw [hfix]; group
    have hw : b⁻¹ * (t⁻¹ * b * t) = (t⁻¹ * a * t)⁻¹ * a := by
      have hc : Commute b ((t⁻¹ * a * t)⁻¹ * a) :=
        (hcomm _ (mul_mem (inv_mem ha1) ha) b hb).symm
      calc b⁻¹ * (t⁻¹ * b * t)
          = b⁻¹ * ((t⁻¹ * a * t)⁻¹ * ((t⁻¹ * a * t) * (t⁻¹ * b * t))) := by group
        _ = b⁻¹ * ((t⁻¹ * a * t)⁻¹ * a * b) := by rw [hfix]; group
        _ = b⁻¹ * (b * ((t⁻¹ * a * t)⁻¹ * a)) := by rw [← hc.eq]
        _ = (t⁻¹ * a * t)⁻¹ * a := by group
    refine ⟨Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem ha) ha1, ?_⟩,
      Subgroup.mem_inf.mpr ⟨?_, mul_mem (inv_mem hb) hb1⟩⟩
    · rw [hz]
      exact mul_mem hb (inv_mem hb1)
    · rw [hw]
      exact mul_mem (inv_mem ha1) ha
  have hdecomp : ∀ x ∈ (A ⊔ B) ⊓ centralizer ({t} : Set H),
      ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
    intro x hx
    have hx1 : x ∈ ((A ⊔ B : Subgroup H) : Set H) := hx.1
    rw [hsup] at hx1
    exact Set.mem_mul.mp hx1
  rw [commutator_le]
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hdecomp x hx
  obtain ⟨a', ha', b', hb', rfl⟩ := hdecomp y hy
  obtain ⟨hz, hw⟩ := hdisp a ha b hb hx.2
  obtain ⟨hz', hw'⟩ := hdisp a' ha' b' hb' hy.2
  rw [commutatorElement_mul_mul_eq_mul (hcomm a ha b hb) (hcomm a ha b' hb')
    (hcomm a' ha' b hb) (hcomm a' ha' b' hb')]
  refine mul_mem_sup (Subgroup.mem_inf.mpr ⟨?_, ?_⟩) (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha ha') (inv_mem ha)) (inv_mem ha')
  · rw [mem_centralizer_singleton_iff_conj, conj_commutatorElement,
      show t⁻¹ * a * t = a * (a⁻¹ * (t⁻¹ * a * t)) by group,
      show t⁻¹ * a' * t = a' * (a'⁻¹ * (t⁻¹ * a' * t)) by group]
    exact commutatorElement_mul_mul_of_commute (hcomm a' ha' _ hz.2).symm
      (hcomm a ha _ hz'.2).symm (hcomm _ hz.1 _ hz'.2)
  · simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hb hb') (inv_mem hb)) (inv_mem hb')
  · rw [mem_centralizer_singleton_iff_conj, conj_commutatorElement,
      show t⁻¹ * b * t = b * (b⁻¹ * (t⁻¹ * b * t)) by group,
      show t⁻¹ * b' * t = b' * (b'⁻¹ * (t⁻¹ * b' * t)) by group]
    exact commutatorElement_mul_mul_of_commute (hcomm _ hw.1 b' hb')
      (hcomm _ hw'.1 b hb) (hcomm _ hw.1 _ hw'.2)

variable [Finite H]

theorem conjugate_pow_mem_orbit (M : Subgroup H) (t : H) (n : ℕ) :
    conjugate M (t ^ n) ∈ Set.range fun i : Fin (orderOf t) => conjugate M (t ^ (i : ℕ)) :=
  ⟨⟨n % orderOf t, Nat.mod_lt _ (orderOf_pos t)⟩, by simp only [pow_mod_orderOf]⟩

theorem conjugate_mem_orbit_iff (M N : Subgroup H) (t : H) :
    conjugate N t ∈ (Set.range fun i : Fin (orderOf t) => conjugate M (t ^ (i : ℕ))) ↔
      N ∈ Set.range fun i : Fin (orderOf t) => conjugate M (t ^ (i : ℕ)) := by
  constructor
  · rintro ⟨i, hi⟩
    have hinv : t⁻¹ = t ^ (orderOf t - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
        Nat.sub_add_cancel (orderOf_pos t), pow_orderOf_eq_one]
    have hN : N = conjugate M (t ^ ((i : ℕ) + (orderOf t - 1))) := by
      rw [← conjugate_conjugate_inv N t, ← hi, conjugate_conjugate, hinv, pow_add]
    rw [hN]
    exact conjugate_pow_mem_orbit M t _
  · rintro ⟨i, rfl⟩
    rw [conjugate_conjugate, ← pow_succ]
    exact conjugate_pow_mem_orbit M t _

omit [Finite H] in
theorem orbit_subset {M : Subgroup H} {t : H} {S : Set (Subgroup H)} (hM : M ∈ S)
    (hS : ∀ N ∈ S, conjugate N t ∈ S) :
    (Set.range fun i : Fin (orderOf t) => conjugate M (t ^ (i : ℕ))) ⊆ S := by
  have h : ∀ n : ℕ, conjugate M (t ^ n) ∈ S := by
    intro n
    induction n with
    | zero => rwa [pow_zero, conjugate_one]
    | succ n ih =>
      rw [pow_succ, ← conjugate_conjugate]
      exact hS _ ih
  rintro _ ⟨i, rfl⟩
  exact h i

theorem le_or_le_of_le_sup {p : ℕ} [Fact p.Prime] {C T X Y : Subgroup H} (hTC : T ≤ C)
    (hT : IsPComponent p (T.subgroupOf C)) (hXC : X ≤ C) (hYC : Y ≤ C)
    (hX : (X.subgroupOf C).IsSubnormal) (hY : (Y.subgroupOf C).IsSubnormal)
    (hle : T ≤ X ⊔ Y) : T ≤ X ∨ T ≤ Y := by
  obtain ⟨N, hN, hTN⟩ := CatalogueBPrimeJoin.exists_le_of_le_sSup p (T.subgroupOf C) hT
    {X.subgroupOf C, Y.subgroupOf C} (by rintro N (rfl | rfl) <;> assumption) (by
      rw [sSup_pair, ← subgroupOf_sup hXC hYC]
      exact comap_mono hle)
  rcases hN with rfl | rfl
  · exact Or.inl (le_of_subgroupOf_le hTC hTN)
  · exact Or.inr (le_of_subgroupOf_le hTC hTN)

theorem le_orbit_join_of_le_sSup {p : ℕ} [Fact p.Prime] {t : H} {T : Subgroup H}
    (hTC : T ≤ centralizer ({t} : Set H))
    (hT : IsPComponent p (T.subgroupOf (centralizer ({t} : Set H)))) :
    ∀ (n : ℕ) (S : Set (Subgroup H)), S.ncard = n → (∀ N ∈ S, IsComponent N) →
      (∀ N, conjugate N t ∈ S ↔ N ∈ S) → T ≤ sSup S →
      ∃ M ∈ S, T ≤ ⨆ i : Fin (orderOf t), conjugate M (t ^ (i : ℕ)) := by
  set C := centralizer ({t} : Set H)
  have hTperf : ⁅T, T⁆ = T := by
    have := CatalogueBHeldSmallCore.pComponent_perfect p _ hT
    have : Group.IsPerfect T := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hTC).toMonoidHom) (subgroupOfEquivOfLe hTC).surjective
    exact isPerfect_iff.mp this
  have hsubC : ∀ S : Set (Subgroup H), (∀ N ∈ S, IsComponent N) →
      ((sSup S ⊓ C).subgroupOf C).IsSubnormal := fun S hS => by
    rw [inf_subgroupOf_right]
    exact (sSup_isSubnormal hS).subgroupOf
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hn hS hSt hTS
  rcases S.eq_empty_or_nonempty with hempty | ⟨M, hM⟩
  · exfalso
    rw [hempty, sSup_empty, le_bot_iff] at hTS
    apply CatalogueBPrimeJoin.pComponent_ne_bot hT
    rw [hTS, bot_subgroupOf]
  set O := Set.range fun i : Fin (orderOf t) => conjugate M (t ^ (i : ℕ)) with hOdef
  have hOS : O ⊆ S := orbit_subset hM fun N hN => (hSt N).mpr hN
  have hMO : M ∈ O := by
    simpa only [pow_zero, conjugate_one] using conjugate_pow_mem_orbit M t 0
  set S' := S \ O with hS'def
  have hS'S : S' ⊆ S := Set.sdiff_subset
  have hS'comp : ∀ N ∈ S', IsComponent N := fun N hN => hS N (hS'S hN)
  have hOcomp : ∀ N ∈ O, IsComponent N := fun N hN => hS N (hOS hN)
  have hS't : ∀ N, conjugate N t ∈ S' ↔ N ∈ S' := fun N => by
    rw [hS'def, Set.mem_sdiff, Set.mem_sdiff, hSt N, conjugate_mem_orbit_iff]
  have hcard : S'.ncard < n := by
    rw [← hn]
    exact Set.ncard_lt_ncard (Set.sdiff_ssubset_left_iff.mpr ⟨M, hM, hMO⟩) S.toFinite
  have hsplit : sSup S = sSup O ⊔ sSup S' := by
    rw [← sSup_union, hS'def, Set.union_sdiff_cancel hOS]
  have hA : ∀ a ∈ sSup O, t⁻¹ * a * t ∈ sSup O := fun a ha =>
    conj_mem_sSup (fun N hN => (conjugate_mem_orbit_iff M N t).mpr hN) ha
  have hB : ∀ b ∈ sSup S', t⁻¹ * b * t ∈ sSup S' := fun b hb =>
    conj_mem_sSup (fun N hN => (hS't N).mpr hN) hb
  have hAB : sSup O ≤ centralizer ((sSup S' : Subgroup H) : Set H) :=
    sSup_le_centralizer_sSup hOcomp hS'comp fun N hN hN' => hN'.2 hN
  have hTsup : T ≤ sSup O ⊓ C ⊔ sSup S' ⊓ C := by
    have hTX : T ≤ (sSup O ⊔ sSup S') ⊓ C := le_inf (hsplit ▸ hTS) hTC
    calc T = ⁅T, T⁆ := hTperf.symm
      _ ≤ ⁅(sSup O ⊔ sSup S') ⊓ C, (sSup O ⊔ sSup S') ⊓ C⁆ := commutator_mono hTX hTX
      _ ≤ _ := commutator_centralizer_sup_le hA hB hAB
  rcases le_or_le_of_le_sup hTC hT inf_le_right inf_le_right (hsubC O hOcomp)
      (hsubC S' hS'comp) hTsup with hTO | hTS'
  · refine ⟨M, hM, ?_⟩
    rw [← sSup_range]
    exact hTO.trans inf_le_left
  · obtain ⟨M', hM', hTM'⟩ := ih _ hcard S' rfl hS'comp hS't (hTS'.trans inf_le_left)
    exact ⟨M', hS'S hM', hTM'⟩

theorem ordinary_layer_local_prime_component_orbit_location {p : ℕ} (hp : p.Prime) {t : H}
    {T : Subgroup H} (hTC : T ≤ centralizer ({t} : Set H))
    (hT : IsPComponent p (T.subgroupOf (centralizer ({t} : Set H)))) (hTE : T ≤ layer H) :
    ∃ M : Subgroup H, IsComponent M ∧
      T ≤ ⨆ i : Fin (orderOf t), conjugate M (t ^ (i : ℕ)) ∧
      IsPComponent p (T.subgroupOf
        ((⨆ i : Fin (orderOf t), conjugate M (t ^ (i : ℕ))) ⊓ centralizer ({t} : Set H))) ∧
      (orderOf t = 2 → ⨆ i : Fin (orderOf t), conjugate M (t ^ (i : ℕ)) = M ⊔ conjugate M t) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨M, hM, hTK⟩ := le_orbit_join_of_le_sSup hTC hT _ {N | IsComponent N} rfl
    (fun N hN => hN) (fun N => isComponent_conjugate_iff N t) hTE
  refine ⟨M, hM, hTK, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hTK hTC)
    inf_le_right hT, fun ht => le_antisymm ?_ ?_⟩
  · refine iSup_le fun i => ?_
    have hi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by have := i.2; omega
    rcases hi with hi | hi
    · rw [hi, pow_zero, conjugate_one]
      exact le_sup_left
    · rw [hi, pow_one]
      exact le_sup_right
  · refine sup_le ?_ ?_
    · have h := le_iSup (fun i : Fin (orderOf t) => conjugate M (t ^ (i : ℕ)))
        ⟨0, orderOf_pos t⟩
      simpa only [pow_zero, conjugate_one] using h
    · have h := le_iSup (fun i : Fin (orderOf t) => conjugate M (t ^ (i : ℕ)))
        ⟨1, by omega⟩
      simpa only [pow_one] using h

end CFSG.ComponentClassification.UnbalancedLayer
