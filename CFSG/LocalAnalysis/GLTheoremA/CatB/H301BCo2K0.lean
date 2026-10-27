module

public import CFSG.Sporadic.Co2I301.Spec
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B.Co2K0

open CFSG.Sporadic.Co2I301
open CFSG.Sporadic.Co2Cert (co2P)
open CFSG.Sporadic.Co2Schreier (locZ)
open scoped commutatorElement

private theorem isA6_perfect_card (i : TauCeti.CFSGIndex) (hi : S8.isA6 i) :
    commutator i.Group = ⊤ ∧ Nat.card i.Group = 360 := by
  rcases hi with hi | hi
  · cases i with
    | alternating n hn =>
      have hn6 : n = 6 := hi
      subst hn6
      have h6 : Nat.card (Fin 6) = 6 := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      show commutator (alternatingGroup (Fin 6)) = ⊤ ∧ Nat.card (alternatingGroup (Fin 6)) = 360
      refine ⟨commutator_alternatingGroup_eq_top (by rw [h6]; norm_num), ?_⟩
      rw [nat_card_alternatingGroup, h6]
      norm_num [Nat.factorial]
    | _ => exact hi.elim
  · cases i with
    | lie j =>
      obtain ⟨d, hv⟩ := j
      cases d with
      | A n q =>
        rcases n with _ | _ | n
        · exact hi.elim
        · have hq : q.card = 9 := hi
          have hdup := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
          rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hdup
          exact (hdup (Or.inl ⟨rfl, Or.inr (Or.inr hq)⟩)).elim
        · exact hi.elim
      | _ => exact hi.elim
    | _ => exact hi.elim

private theorem commutatorElement_eq_of_commute {G : Type*} [Group G] {t u : G}
    (htu : Commute t u) (g h : G) :
    ⁅g, h⁆ = g * t⁻¹ * (t * (h * u⁻¹) * t⁻¹) * (u * (g * t⁻¹)⁻¹ * u⁻¹) * (h * u⁻¹)⁻¹ := by
  have h1 : t * u * t⁻¹ * u⁻¹ = 1 := by rw [htu.eq, mul_inv_cancel_right, mul_inv_cancel]
  calc ⁅g, h⁆ = g * t⁻¹ * (t * (h * u⁻¹) * t⁻¹) * (t * u * t⁻¹ * u⁻¹) *
        (u * (g * t⁻¹)⁻¹ * u⁻¹) * (h * u⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    _ = _ := by rw [h1, mul_one]

private theorem commute_pow_mul {G : Type*} [Group G] {a b c : G} (hab : Commute a b)
    (hac : Commute a c) (hbc : Commute b c) (i j k i' j' k' : ℕ) :
    Commute (a ^ i * b ^ j * c ^ k) (a ^ i' * b ^ j' * c ^ k') := by
  have h : ∀ x : G, Commute x a → Commute x b → Commute x c →
      Commute x (a ^ i' * b ^ j' * c ^ k') := fun x ha hb hc =>
    ((ha.pow_right i').mul_right (hb.pow_right j')).mul_right (hc.pow_right k')
  exact (((h a (Commute.refl a) hab hac).pow_left i).mul_left
    ((h b hab.symm (Commute.refl b) hbc).pow_left j)).mul_left
    ((h c hac.symm hbc.symm (Commute.refl c)).pow_left k)

private def normK0 : Submonoid (Equiv.Perm (Fin 2300)) where
  carrier := {g | ∀ x ∈ K0, g * x * g⁻¹ ∈ K0}
  mul_mem' {a b} ha hb := by
    intro x hx
    simpa only [mul_inv_rev, mul_assoc] using ha _ (hb x hx)
  one_mem' := by
    intro x hx
    simpa using hx

private theorem mem_normK0 {g : Equiv.Perm (Fin 2300)} (h1 : g * k1P * g⁻¹ ∈ K0)
    (h2 : g * k2P * g⁻¹ ∈ K0) : g ∈ normK0 := by
  intro x hx
  have hle : (Subgroup.closure {k1P, k2P}).map (MulAut.conj g).toMonoidHom ≤ K0 := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl
    exacts [h1, h2]
  exact hle (Subgroup.mem_map_of_mem _ hx)

section Facts


private theorem pow_mul_mem_normK0 (i j k : ℕ) : dP ^ i * locZ ^ j * sP ^ k ∈ normK0 := by
  obtain ⟨-, -, -, hdk1, hdk2, -, -, -, -, -, hzk1, hzk2⟩ := commute_facts
  obtain ⟨-, -, hs1, hs2⟩ := mem_K0_facts
  have hk1 : k1P ∈ K0 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hk2 : k2P ∈ K0 := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hd : dP ∈ normK0 := mem_normK0 (by rw [hdk1.mul_inv_cancel]; exact hk1)
    (by rw [hdk2.mul_inv_cancel]; exact hk2)
  have hz : locZ ∈ normK0 := mem_normK0 (by rw [hzk1.mul_inv_cancel]; exact hk1)
    (by rw [hzk2.mul_inv_cancel]; exact hk2)
  exact mul_mem (mul_mem (pow_mem hd i) (pow_mem hz j)) (pow_mem (mem_normK0 hs1 hs2) k)

private theorem commutatorElement_mem_K0 {g h : Equiv.Perm (Fin 2300)} (hgP : g ∈ co2P)
    (hgd : Commute g dP) (hgz : Commute g locZ) (hhP : h ∈ co2P) (hhd : Commute h dP)
    (hhz : Commute h locZ) : ⁅g, h⁆ ∈ K0 := by
  obtain ⟨hds, -, -, -, -, -, hzd, hzs, -⟩ := commute_facts
  obtain ⟨⟨a, b, c, -, -, -, hg⟩, -⟩ := centralizer_facts g hgP hgd hgz
  obtain ⟨⟨a', b', c', -, -, -, hh⟩, -⟩ := centralizer_facts h hhP hhd hhz
  rw [commutatorElement_eq_of_commute (commute_pow_mul hzd.symm hds hzs a b c a' b' c')]
  exact K0.mul_mem (K0.mul_mem (K0.mul_mem hg (pow_mul_mem_normK0 a b c _ hh))
    (pow_mul_mem_normK0 a' b' c' _ (K0.inv_mem hg))) (K0.inv_mem hh)

theorem K0_le_of_quotient_A6 {K : Subgroup (Equiv.Perm (Fin 2300))} (hKP : K ≤ co2P)
    (hKd : K ≤ Subgroup.centralizer ({dP} : Set (Equiv.Perm (Fin 2300))))
    (hKz : K ≤ Subgroup.centralizer ({locZ} : Set (Equiv.Perm (Fin 2300))))
    (hK : MapsOntoType K S8.isA6) : K0 ≤ K := by
  obtain ⟨i, hi, f, hf⟩ := hK
  obtain ⟨htop, hcard⟩ := isA6_perfect_card i hi
  have hle : (commutator K).map K.subtype ≤ K0 := by
    rw [commutator_eq_closure, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, hx, rfl⟩
    obtain ⟨g, h, rfl⟩ := mem_commutatorSet_iff.1 hx
    rw [map_commutatorElement]
    exact commutatorElement_mem_K0 (hKP g.2) (Subgroup.mem_centralizer_singleton_iff.1 (hKd g.2))
      (Subgroup.mem_centralizer_singleton_iff.1 (hKz g.2)) (hKP h.2)
      (Subgroup.mem_centralizer_singleton_iff.1 (hKd h.2))
      (Subgroup.mem_centralizer_singleton_iff.1 (hKz h.2))
  have hmap : (commutator K).map f = ⊤ := by
    rw [commutator, Subgroup.map_commutator, Subgroup.map_top_of_surjective f hf]
    exact htop
  have hcardle : Nat.card K0 ≤ Nat.card ((commutator K).map K.subtype) := by
    rw [card_K0, Subgroup.card_subtype, ← hcard, ← Subgroup.card_top (G := i.Group), ← hmap]
    exact Nat.card_le_card_of_surjective _ (f.subgroupMap_surjective _)
  rw [← Subgroup.eq_of_le_of_card_ge hle hcardle]
  exact Subgroup.map_subtype_le _

end Facts

end CFSG.LocalAnalysis.GLTheoremA.H301B.Co2K0

end
