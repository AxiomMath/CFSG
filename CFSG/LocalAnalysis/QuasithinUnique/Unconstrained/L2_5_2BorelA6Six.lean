module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6Enc
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.QuasithinUnique.Borel252.A6

open Equiv

abbrev A6s : Subgroup P6 := alternatingGroup (Fin 6)

def D0 : Subgroup P6 := Subgroup.closure {g | g ∈ d0Gens}

def Sa : Subgroup P6 := Subgroup.closure {g | g ∈ saGens}

def Sb : Subgroup P6 := Subgroup.closure {g | g ∈ sbGens}

def VA : Subgroup P6 := Subgroup.closure {g | g ∈ vaGens}

def VB : Subgroup P6 := Subgroup.closure {g | g ∈ vbGens}

theorem sound_D0 : ∀ r ∈ d0L, ∃ x ∈ D0, R6.enc x = r := iterL_sound rawIsEnc d0Gens 4

theorem sound_Sa : ∀ r ∈ saL, ∃ x ∈ Sa, R6.enc x = r := iterL_sound rawIsEnc saGens 5

theorem sound_Sb : ∀ r ∈ sbL, ∃ x ∈ Sb, R6.enc x = r := iterL_sound rawIsEnc sbGens 5

theorem sound_VA : ∀ r ∈ vaL, ∃ x ∈ VA, R6.enc x = r := iterL_sound rawIsEnc vaGens 3

theorem sound_VB : ∀ r ∈ vbL, ∃ x ∈ VB, R6.enc x = r := iterL_sound rawIsEnc vbGens 3

theorem mem_D0 (x : P6) : x ∈ D0 ↔ R6.enc x ∈ d0L := by
  obtain ⟨h1, hcl⟩ := closedB_spec closed_ok.1
  exact mem_closure_iff_of_closed rawIsEnc d0Gens d0L h1 hcl sound_D0 x

theorem mem_Sa (x : P6) : x ∈ Sa ↔ R6.enc x ∈ saL := by
  obtain ⟨h1, hcl⟩ := closedB_spec closed_ok.2.1
  exact mem_closure_iff_of_closed rawIsEnc saGens saL h1 hcl sound_Sa x

theorem mem_Sb (x : P6) : x ∈ Sb ↔ R6.enc x ∈ sbL := by
  obtain ⟨h1, hcl⟩ := closedB_spec closed_ok.2.2.1
  exact mem_closure_iff_of_closed rawIsEnc sbGens sbL h1 hcl sound_Sb x

theorem mem_VA (x : P6) : x ∈ VA ↔ R6.enc x ∈ vaL := by
  obtain ⟨h1, hcl⟩ := closedB_spec closed_ok.2.2.2.1
  exact mem_closure_iff_of_closed rawIsEnc vaGens vaL h1 hcl sound_VA x

theorem mem_VB (x : P6) : x ∈ VB ↔ R6.enc x ∈ vbL := by
  obtain ⟨h1, hcl⟩ := closedB_spec closed_ok.2.2.2.2
  exact mem_closure_iff_of_closed rawIsEnc vbGens vbL h1 hcl sound_VB x

theorem card_D0 : Nat.card D0 = 8 := by
  obtain ⟨hd, -, -, hdn, -, -, -, -, -, -⟩ := sizes_ok
  rw [card_of_list R6.enc_inj D0 d0L hdn mem_D0 (fun r hr => (sound_D0 r hr).imp fun x hx => hx.2)]
  exact hd

theorem card_VA : Nat.card VA = 4 := by
  obtain ⟨-, -, -, -, -, -, hva, -, hvan, -⟩ := sizes_ok
  rw [card_of_list R6.enc_inj VA vaL hvan mem_VA (fun r hr => (sound_VA r hr).imp fun x hx => hx.2)]
  exact hva

theorem card_VB : Nat.card VB = 4 := by
  obtain ⟨-, -, -, -, -, -, -, hvb, -, hvbn⟩ := sizes_ok
  rw [card_of_list R6.enc_inj VB vbL hvbn mem_VB (fun r hr => (sound_VB r hr).imp fun x hx => hx.2)]
  exact hvb

theorem card_A6 : Nat.card A6s = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem D0_le_A6 : D0 ≤ A6s := by
  obtain ⟨h, -⟩ := gens_even
  rw [D0, Subgroup.closure_le]
  intro g hg
  exact Equiv.Perm.mem_alternatingGroup.2 (h g hg)

theorem Sa_le_A6 : Sa ≤ A6s := by
  obtain ⟨-, h, -⟩ := gens_even
  rw [Sa, Subgroup.closure_le]
  intro g hg
  exact Equiv.Perm.mem_alternatingGroup.2 (h g hg)

theorem Sb_le_A6 : Sb ≤ A6s := by
  obtain ⟨-, -, h, -⟩ := gens_even
  rw [Sb, Subgroup.closure_le]
  intro g hg
  exact Equiv.Perm.mem_alternatingGroup.2 (h g hg)

theorem VA_le_D0 : VA ≤ D0 := fun x hx => (mem_D0 x).2 (sub_ok.1 _ ((mem_VA x).1 hx))

theorem VB_le_D0 : VB ≤ D0 := fun x hx => (mem_D0 x).2 (sub_ok.2.1 _ ((mem_VB x).1 hx))

theorem D0_le_Sa : D0 ≤ Sa := fun x hx => (mem_Sa x).2 (sub_ok.2.2.1 _ ((mem_D0 x).1 hx))

theorem D0_le_Sb : D0 ≤ Sb := fun x hx => (mem_Sb x).2 (sub_ok.2.2.2 _ ((mem_D0 x).1 hx))

theorem VA_le_A6 : VA ≤ A6s := VA_le_D0.trans D0_le_A6

theorem VB_le_A6 : VB ≤ A6s := VB_le_D0.trans D0_le_A6

theorem sup_VA_VB : VA ⊔ VB = D0 := by
  refine le_antisymm (sup_le VA_le_D0 VB_le_D0) ?_
  rw [D0, Subgroup.closure_le]
  intro g hg
  obtain ⟨a, ha, b, hb, hab⟩ := sup_ok g hg
  obtain ⟨a', ha', rfl⟩ := sound_VA a ha
  obtain ⟨b', hb', rfl⟩ := sound_VB b hb
  have : g = a' * b' := R6.enc_inj (by rw [R6.enc_mul]; exact hab)
  rw [SetLike.mem_coe, this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha') (Subgroup.mem_sup_right hb')

theorem mem_map_conj {G : Type*} [Group G] (Y : Subgroup G) (g x : G) :
    x ∈ Y.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ Y := by
  have hc : ∀ y, (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ := fun y => rfl
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [hc, e]
    exact hy
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    rw [hc]
    group

theorem conj_stable_iff {G : Type*} [Group G] [Finite G] (Y : Subgroup G) (τ : G)
    (h : ∀ y ∈ Y, τ * y * τ⁻¹ ∈ Y) : ∀ p, p ∈ Y ↔ τ * p * τ⁻¹ ∈ Y := by
  intro p
  refine ⟨h p, fun hp => ?_⟩
  have hle : Y.map (MulAut.conj τ).toMonoidHom ≤ Y := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have heq : Y.map (MulAut.conj τ).toMonoidHom = Y :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj τ).injective])
  have hp' : τ * p * τ⁻¹ ∈ Y.map (MulAut.conj τ).toMonoidHom := by
    rw [heq]
    exact hp
  have h1 := (mem_map_conj Y τ _).1 hp'
  have e : τ⁻¹ * (τ * p * τ⁻¹) * τ = p := by group
  rwa [e] at h1

theorem conj_stable_of_gens {G : Type*} [Group G] (gens : List G) (τ : G)
    (h : ∀ g ∈ gens, τ * g * τ⁻¹ ∈ Subgroup.closure {g | g ∈ gens}) :
    ∀ y ∈ Subgroup.closure {g | g ∈ gens}, τ * y * τ⁻¹ ∈ Subgroup.closure {g | g ∈ gens} := by
  have : Subgroup.closure {g | g ∈ gens} ≤
      (Subgroup.closure {g | g ∈ gens}).comap (MulAut.conj τ).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro g hg
    exact h g hg
  exact fun y hy => this hy

theorem six_overgroups (Y : Subgroup P6) (hD : D0 ≤ Y) (hA : Y ≤ A6s) :
    Y = D0 ∨ Y = Sa ∨ Y = Sb ∨ Y = A6s := by
  classical
  set S : Finset (Fin 9) := Finset.univ.filter (fun i => rep i ∈ Y) with hS
  have hmemS : ∀ i, i ∈ S ↔ rep i ∈ Y := fun i => by simp [hS]
  have key : ∀ x ∈ A6s, ∃ i : Fin 9, ∃ d ∈ D0, ∃ e ∈ D0, x = d * rep i * e := by
    intro x hx
    obtain ⟨i, d, hd, e, he, h⟩ := cover_ok x (Equiv.Perm.mem_alternatingGroup.1 hx)
    obtain ⟨d', hd', rfl⟩ := sound_D0 d hd
    obtain ⟨e', he', rfl⟩ := sound_D0 e he
    exact ⟨i, d', hd', e', he', R6.enc_inj (by rw [R6.enc_mul, R6.enc_mul]; exact h)⟩
  have hmemY : ∀ (x : P6) (i : Fin 9), ∀ d ∈ D0, ∀ e ∈ D0, x = d * rep i * e → (x ∈ Y ↔ i ∈ S) := by
    intro x i d hd e he hx'
    rw [hmemS]
    constructor
    · intro hxY
      have : rep i = d⁻¹ * x * e⁻¹ := by rw [hx']; group
      rw [this]
      exact Y.mul_mem (Y.mul_mem (Y.inv_mem (hD hd)) hxY) (Y.inv_mem (hD he))
    · intro hr
      rw [hx']
      exact Y.mul_mem (Y.mul_mem (hD hd) hr) (hD he)
  have h0 : (0 : Fin 9) ∈ S := (hmemS 0).2 (by rw [rep_facts.1]; exact Y.one_mem)
  have hcl : ∀ t ∈ tabE, t.i ∈ S → t.j ∈ S → t.k ∈ S := by
    intro t ht hi hj
    obtain ⟨hw, hd, he, heq⟩ := tab_ok t ht
    have hw' := (mem_D0 _).2 hw
    have hd' := (mem_D0 _).2 hd
    have he' := (mem_D0 _).2 he
    have heq' : rep t.i * t.w * rep t.j = t.d * rep t.k * t.e :=
      R6.enc_inj (by rw [R6.enc_mul, R6.enc_mul, R6.enc_mul, R6.enc_mul]; exact heq)
    have hi' := (hmemS _).1 hi
    have hj' := (hmemS _).1 hj
    have hprod : t.d * rep t.k * t.e ∈ Y := by
      rw [← heq']
      exact Y.mul_mem (Y.mul_mem hi' (hD hw')) hj'
    exact (hmemY _ t.k t.d hd' t.e he' rfl).1 hprod
  rcases lattice_ok S h0 hcl with h | h | h | h
  · left
    refine le_antisymm (fun y hy => ?_) hD
    obtain ⟨i, d, hd, e, he, hy'⟩ := key y (hA hy)
    have hiS := (hmemY y i d hd e he hy').1 hy
    rw [h, Finset.mem_singleton] at hiS
    subst hiS
    rw [hy', rep_facts.1, mul_one]
    exact D0.mul_mem hd he
  · right; left
    refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨i, d, hd, e, he, hy'⟩ := key y (hA hy)
      have hiS := (hmemY y i d hd e he hy').1 hy
      rw [h] at hiS
      have hSa : ∀ z ∈ D0, z ∈ Sa := fun z hz => D0_le_Sa hz
      rcases Finset.mem_insert.1 hiS with rfl | hi2
      · rw [hy', rep_facts.1, mul_one]
        exact hSa _ (D0.mul_mem hd he)
      · rw [Finset.mem_singleton] at hi2
        subst hi2
        rw [hy']
        exact Sa.mul_mem (Sa.mul_mem (D0_le_Sa hd) ((mem_Sa _).2 rep_facts.2.1)) (D0_le_Sa he)
    · obtain ⟨i, hi, d, hd, e, he, hy'⟩ := sa_cover (R6.enc y) ((mem_Sa y).1 hy)
      obtain ⟨d', hd', rfl⟩ := sound_D0 d hd
      obtain ⟨e', he', rfl⟩ := sound_D0 e he
      have hy'' : y = d' * rep i * e' :=
        R6.enc_inj (by rw [R6.enc_mul, R6.enc_mul]; exact hy')
      have hiS : i ∈ S := by
        rw [h]
        rcases hi with rfl | rfl <;> simp
      exact (hmemY y i d' hd' e' he' hy'').2 hiS
  · right; right; left
    refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨i, d, hd, e, he, hy'⟩ := key y (hA hy)
      have hiS := (hmemY y i d hd e he hy').1 hy
      rw [h] at hiS
      rcases Finset.mem_insert.1 hiS with rfl | hi2
      · rw [hy', rep_facts.1, mul_one]
        exact D0_le_Sb (D0.mul_mem hd he)
      · rw [Finset.mem_singleton] at hi2
        subst hi2
        rw [hy']
        exact Sb.mul_mem (Sb.mul_mem (D0_le_Sb hd) ((mem_Sb _).2 rep_facts.2.2)) (D0_le_Sb he)
    · obtain ⟨i, hi, d, hd, e, he, hy'⟩ := sb_cover (R6.enc y) ((mem_Sb y).1 hy)
      obtain ⟨d', hd', rfl⟩ := sound_D0 d hd
      obtain ⟨e', he', rfl⟩ := sound_D0 e he
      have hy'' : y = d' * rep i * e' :=
        R6.enc_inj (by rw [R6.enc_mul, R6.enc_mul]; exact hy')
      have hiS : i ∈ S := by
        rw [h]
        rcases hi with rfl | rfl <;> simp
      exact (hmemY y i d' hd' e' he' hy'').2 hiS
  · right; right; right
    refine le_antisymm hA (fun x hx => ?_)
    obtain ⟨i, d, hd, e, he, hx'⟩ := key x hx
    exact (hmemY x i d hd e he hx').2 (by rw [h]; exact Finset.mem_univ i)

theorem conjIn_iff {Y : Subgroup P6} {L : List R6} (hmem : ∀ x, x ∈ Y ↔ R6.enc x ∈ L)
    (hs : ∀ r ∈ L, ∃ x, R6.enc x = r) (τ g : P6) :
    conjIn (R6.enc τ) L (R6.enc g) = true ↔ τ * g * τ⁻¹ ∈ Y := by
  simp only [conjIn, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨y, hy, hyτ⟩
    obtain ⟨y', hy'⟩ := hs y hy
    rw [← hy', ← R6.enc_mul, ← R6.enc_mul] at hyτ
    have h1 := R6.enc_inj hyτ
    have h2 : y' ∈ Y := (hmem y').2 (hy' ▸ hy)
    have h3 : τ * g * τ⁻¹ = y' := by
      rw [mul_inv_eq_iff_eq_mul, h1]
    rwa [h3]
  · intro h
    refine ⟨R6.enc (τ * g * τ⁻¹), (hmem _).1 h, ?_⟩
    rw [← R6.enc_mul, ← R6.enc_mul]
    congr 1
    group

theorem norm_D0 (x : P6) (hx : x ∈ A6s) : x ∈ Subgroup.normalizer (D0 : Set P6) ↔ x ∈ D0 := by
  constructor
  · intro hn
    have hall : (d0Gens.map R6.enc).all (conjIn (R6.enc x) d0L) = true := by
      rw [List.all_eq_true]
      intro g' hg'
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
      exact (conjIn_iff mem_D0 (fun r hr => (sound_D0 r hr).imp fun y hy => hy.2) x g).2
        ((Subgroup.mem_normalizer_iff.mp hn g).mp (Subgroup.subset_closure hg))
    exact (mem_D0 x).2 (normD0_ok x (Equiv.Perm.mem_alternatingGroup.1 hx) hall)
  · intro h
    exact Subgroup.le_normalizer h

theorem norm_VA (x : P6) (hx : x ∈ A6s) : x ∈ Subgroup.normalizer (VA : Set P6) ↔ x ∈ Sa := by
  constructor
  · intro hn
    have hall : (vaGens.map R6.enc).all (conjIn (R6.enc x) vaL) = true := by
      rw [List.all_eq_true]
      intro g' hg'
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
      exact (conjIn_iff mem_VA (fun r hr => (sound_VA r hr).imp fun y hy => hy.2) x g).2
        ((Subgroup.mem_normalizer_iff.mp hn g).mp (Subgroup.subset_closure hg))
    exact (mem_Sa x).2 (normVa_ok x (Equiv.Perm.mem_alternatingGroup.1 hx) hall)
  · intro hs
    have hgen : ∀ g ∈ saGens, g ∈ Subgroup.normalizer (VA : Set P6) := by
      intro g hg
      have hc : ∀ v ∈ vaGens, g * v * g⁻¹ ∈ VA := fun v hv =>
        (conjIn_iff mem_VA (fun r hr => (sound_VA r hr).imp fun y hy => hy.2) g v).1
          (SN_ok.1 (R6.enc g) (List.mem_map_of_mem hg) (R6.enc v) (List.mem_map_of_mem hv))
      rw [Subgroup.mem_normalizer_iff]
      exact conj_stable_iff VA g (conj_stable_of_gens vaGens g hc)
    have : Sa ≤ Subgroup.normalizer (VA : Set P6) := by
      rw [Sa, Subgroup.closure_le]
      exact hgen
    exact this hs

theorem norm_VB (x : P6) (hx : x ∈ A6s) : x ∈ Subgroup.normalizer (VB : Set P6) ↔ x ∈ Sb := by
  constructor
  · intro hn
    have hall : (vbGens.map R6.enc).all (conjIn (R6.enc x) vbL) = true := by
      rw [List.all_eq_true]
      intro g' hg'
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
      exact (conjIn_iff mem_VB (fun r hr => (sound_VB r hr).imp fun y hy => hy.2) x g).2
        ((Subgroup.mem_normalizer_iff.mp hn g).mp (Subgroup.subset_closure hg))
    exact (mem_Sb x).2 (normVb_ok x (Equiv.Perm.mem_alternatingGroup.1 hx) hall)
  · intro hs
    have hgen : ∀ g ∈ sbGens, g ∈ Subgroup.normalizer (VB : Set P6) := by
      intro g hg
      have hc : ∀ v ∈ vbGens, g * v * g⁻¹ ∈ VB := fun v hv =>
        (conjIn_iff mem_VB (fun r hr => (sound_VB r hr).imp fun y hy => hy.2) g v).1
          (SN_ok.2 (R6.enc g) (List.mem_map_of_mem hg) (R6.enc v) (List.mem_map_of_mem hv))
      rw [Subgroup.mem_normalizer_iff]
      exact conj_stable_iff VB g (conj_stable_of_gens vbGens g hc)
    have : Sb ≤ Subgroup.normalizer (VB : Set P6) := by
      rw [Sb, Subgroup.closure_le]
      exact hgen
    exact this hs

theorem cent_VA {x : P6} (hx : x ∈ A6s) (h : ∀ v ∈ VA, x * v = v * x) : x ∈ VA := by
  rw [mem_VA]
  apply centA_ok x (Equiv.Perm.mem_alternatingGroup.1 hx)
  intro v hv
  have := h v (Subgroup.subset_closure hv)
  rw [← R6.enc_mul, ← R6.enc_mul, this]

theorem cent_VB {x : P6} (hx : x ∈ A6s) (h : ∀ v ∈ VB, x * v = v * x) : x ∈ VB := by
  rw [mem_VB]
  apply centB_ok x (Equiv.Perm.mem_alternatingGroup.1 hx)
  intro v hv
  have := h v (Subgroup.subset_closure hv)
  rw [← R6.enc_mul, ← R6.enc_mul, this]

theorem core_VA {c : P6} (hc : c ∈ D0) (h : ∀ g ∈ Sa, g * c * g⁻¹ ∈ D0) : c ∈ VA := by
  rw [mem_VA]
  apply core_ok.1 (R6.enc c) ((mem_D0 c).1 hc)
  intro g' hg'
  obtain ⟨x, hx, rfl⟩ := sound_Sa g' hg'
  exact (conjIn_iff mem_D0 (fun r hr => (sound_D0 r hr).imp fun y hy => hy.2) x c).2 (h x hx)

theorem core_VB {c : P6} (hc : c ∈ D0) (h : ∀ g ∈ Sb, g * c * g⁻¹ ∈ D0) : c ∈ VB := by
  rw [mem_VB]
  apply core_ok.2 (R6.enc c) ((mem_D0 c).1 hc)
  intro g' hg'
  obtain ⟨x, hx, rfl⟩ := sound_Sb g' hg'
  exact (conjIn_iff mem_D0 (fun r hr => (sound_D0 r hr).imp fun y hy => hy.2) x c).2 (h x hx)

theorem center_A6 {x : P6} (hx : x ∈ A6s) (h : ∀ y ∈ A6s, x * y = y * x) : x = 1 := by
  obtain ⟨-, -, -, -, -, h1, h2⟩ := gens_even
  have e1 := h cenG1 (Equiv.Perm.mem_alternatingGroup.2 h1)
  have e2 := h cenG2 (Equiv.Perm.mem_alternatingGroup.2 h2)
  apply R6.enc_inj
  rw [R6.enc_one]
  apply center_ok x (Equiv.Perm.mem_alternatingGroup.1 hx)
  · rw [← R6.enc_mul, ← R6.enc_mul, e1]
  · rw [← R6.enc_mul, ← R6.enc_mul, e2]

end CFSG.QuasithinUnique.Borel252.A6
