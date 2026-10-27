module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourConj
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Single
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Defs

public section

namespace CFSG.QuasithinUnique.A5.S2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def cj (t : G) (L : Subgroup G) : Subgroup G := L.map (MulAut.conj t).toMonoidHom

theorem mem_cj {t x : G} {L : Subgroup G} : x ∈ cj t L ↔ t⁻¹ * x * t ∈ L := by
  unfold cj
  have := (Subgroup.mem_map_equiv (f := MulAut.conj t) (K := L) (x := x))
  simpa [MulAut.conj_symm_apply] using this

theorem mem_cj_iff {t x : G} {L : Subgroup G} : x ∈ cj t L ↔ ∃ y ∈ L, x = t * y * t⁻¹ := by
  rw [mem_cj]
  constructor
  · intro h
    exact ⟨_, h, by group⟩
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy

theorem mul_mul_inv_mem_cj {t y : G} {L : Subgroup G} (hy : y ∈ L) : t * y * t⁻¹ ∈ cj t L :=
  mem_cj_iff.2 ⟨y, hy, rfl⟩

theorem cj_cj (s t : G) (L : Subgroup G) : cj s (cj t L) = cj (s * t) L := by
  ext x
  rw [mem_cj, mem_cj, mem_cj]
  constructor <;> intro h <;> simpa [mul_assoc] using h

theorem cj_one (L : Subgroup G) : cj 1 L = L := by
  ext x
  rw [mem_cj]
  simp

theorem conjR_eq_cj (L : Subgroup G) (g : G) : conjR L g = cj g⁻¹ L := rfl

theorem card_cj [Finite G] (t : G) (L : Subgroup G) : Nat.card (cj t L) = Nat.card L :=
  Nat.card_congr (Subgroup.equivMapOfInjective L _ (MulAut.conj t).injective).toEquiv.symm

theorem cj_mono {t : G} {A B : Subgroup G} (h : A ≤ B) : cj t A ≤ cj t B :=
  Subgroup.map_mono h

theorem mem_normalizer_iff_cj {x : G} {L : Subgroup G} :
    x ∈ Subgroup.normalizer (L : Set G) ↔ cj x L = L := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rfl

section Blocks

theorem perfect_of_alt5 {L : Subgroup G} (hL : IsShort2 L) (h5 : IsAltType L 5) : ⁅L, L⁆ = L := by
  obtain ⟨α, hα, hαk, -⟩ := h5
  have hQ : commutator ↥(alternatingGroup (Fin 5)) = ⊤ :=
    commutator_alternatingGroup_eq_top (by simp)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Subgroup.isPerfect_iff, Group.isPerfect_def]
  apply C1GN.isShort2_eq_top_of_sup_pCore hL (commutator ↥L)
  have hmap : (commutator ↥L).map α = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hα]
    exact hQ
  have h := Subgroup.comap_map_eq α (commutator ↥L)
  rw [hmap, Subgroup.comap_top, hαk] at h
  exact h.symm

theorem le_or_le_of_normal_block {L L₂ B : Subgroup G} (hL : IsShort2 L) (h5 : IsAltType L 5)
    (hB : IsShort2 B) (hcomm : ∀ a ∈ L, ∀ b ∈ L₂, a * b = b * a) (hBL₀ : B ≤ L ⊔ L₂)
    (hBn : L ⊔ L₂ ≤ Subgroup.normalizer (B : Set G)) : L ≤ B ∨ B ≤ L₂ := by
  classical
  have hLn₂ : L ≤ Subgroup.normalizer (L₂ : Set G) := C5.le_normalizer_of_commute hcomm
  have hL₂n : L₂ ≤ Subgroup.normalizer (L : Set G) :=
    C5.le_normalizer_of_commute fun u hu a ha => (hcomm a ha u hu).symm
  have hL₀L₂ : L ⊔ L₂ ≤ Subgroup.normalizer (L₂ : Set G) := sup_le hLn₂ Subgroup.le_normalizer
  have hL₀L : L ⊔ L₂ ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hL₂n
  have hLL₀ : L ≤ L ⊔ L₂ := le_sup_left
  have hL₂L₀ : L₂ ≤ L ⊔ L₂ := le_sup_right
  set Y : Subgroup G := B ⊔ L₂ with hYdef
  have hYn : ∀ z ∈ L, z ∈ Subgroup.normalizer (Y : Set G) := fun z hz =>
    C1.mem_normalizer_sup (hBn (hLL₀ hz)) (hLn₂ hz)
  have hYmem : ∀ y ∈ Y, ∃ b ∈ B, ∃ c ∈ L₂, y = b * c := fun y hy =>
    (Lin2.mem_sup_iff_of_le_normalizer (hL₂L₀.trans hBn)).1 hy
  by_cases hLY : L ≤ Y
  · left
    have hcl : ∀ ℓ ∈ L, ∀ z ∈ L, ℓ * z * ℓ⁻¹ * z⁻¹ ∈ B := by
      intro ℓ hℓ z hz
      obtain ⟨b, hb, c, hc, rfl⟩ := hYmem ℓ (hLY hℓ)
      have hcz : c * z = z * c := (hcomm z hz c hc).symm
      have e : b * c * z * (b * c)⁻¹ * z⁻¹ = b * (z * b⁻¹ * z⁻¹) := by
        have h1 : c * z * c⁻¹ = z := by rw [hcz]; group
        calc b * c * z * (b * c)⁻¹ * z⁻¹ = b * (c * z * c⁻¹) * b⁻¹ * z⁻¹ := by group
          _ = b * z * b⁻¹ * z⁻¹ := by rw [h1]
          _ = b * (z * b⁻¹ * z⁻¹) := by group
      rw [e]
      refine B.mul_mem hb ?_
      have := (Subgroup.mem_normalizer_iff.mp (hBn (hLL₀ hz)) b⁻¹).1 (B.inv_mem hb)
      simpa using this
    have hperf : ⁅L, L⁆ = L := perfect_of_alt5 hL h5
    have : ⁅L, L⁆ ≤ B := Subgroup.commutator_le.2 fun ℓ hℓ z hz => by
      have := hcl ℓ hℓ z hz
      simpa [commutatorElement_def] using this
    rw [hperf] at this
    exact this
  · right
    set N' : Subgroup G := Y ⊓ L with hN'def
    have hN'L : N' ≤ L := inf_le_right
    have hN'n : (N'.subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hN'L).mpr fun z hz =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨hYn z hz, Subgroup.le_normalizer hz⟩
    have hN'ne : N'.subgroupOf L ≠ ⊤ := by
      intro h
      apply hLY
      intro x hx
      have : (⟨x, hx⟩ : ↥L) ∈ N'.subgroupOf L := h ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 this).1
    obtain ⟨α, hα, hαk, -⟩ := h5
    have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
      C1GN.isSimpleGroup_alternating_of_odd (by decide) (by decide)
    have := hN'n
    have hmapn : ((N'.subgroupOf L).map α).Normal := Subgroup.Normal.map hN'n α hα
    have hmap0 : (N'.subgroupOf L).map α = ⊥ := by
      rcases hsimple.eq_bot_or_eq_top_of_normal ((N'.subgroupOf L).map α) with h | h
      · exact h
      · exfalso
        apply hN'ne
        apply C1GN.isShort2_eq_top_of_sup_pCore hL
        have := Subgroup.comap_map_eq α (N'.subgroupOf L)
        rw [h, Subgroup.comap_top] at this
        rw [← hαk]
        have hker : (N'.subgroupOf L) ⊔ α.ker = ⊤ := this.symm
        exact hker
    have hN'Q : ∀ n ∈ N', ∃ k : ℕ, n ^ 2 ^ k = 1 := by
      intro n hn
      have hnL : n ∈ L := hN'L hn
      have hmem : (⟨n, hnL⟩ : ↥L) ∈ α.ker := by
        rw [MonoidHom.mem_ker]
        have : α ⟨n, hnL⟩ ∈ (N'.subgroupOf L).map α := ⟨⟨n, hnL⟩, hn, rfl⟩
        rw [hmap0] at this
        exact Subgroup.mem_bot.1 this
      rw [hαk] at hmem
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hmem⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hpow : ∀ b ∈ B, ∃ k : ℕ, b ^ 2 ^ k ∈ L₂ := by
      intro b hb
      obtain ⟨ℓ, hℓ, c, hc, hbc⟩ := (Lin2.mem_sup_iff_of_le_normalizer hL₂n).1 (hBL₀ hb)
      have hℓY : ℓ ∈ Y := by
        have : ℓ = b * c⁻¹ := by rw [hbc]; group
        rw [this]
        exact Y.mul_mem (Subgroup.mem_sup_left hb) (Y.inv_mem (Subgroup.mem_sup_right hc))
      obtain ⟨k, hk⟩ := hN'Q ℓ ⟨hℓY, hℓ⟩
      refine ⟨k, ?_⟩
      have hcm : Commute ℓ c := hcomm ℓ hℓ c hc
      rw [hbc, hcm.mul_pow, hk, one_mul]
      exact L₂.pow_mem hc _
    have hB₂n : (L₂.subgroupOf B).Normal := ⟨fun n hn g => by
      have hn' : (n : G) ∈ L₂ := hn
      have hg : (g : G) ∈ Subgroup.normalizer (L₂ : Set G) := hL₀L₂ (hBL₀ g.2)
      have := (Subgroup.mem_normalizer_iff.mp hg (n : G)).1 hn'
      show ((g * n * g⁻¹ : B) : G) ∈ L₂
      simpa using this⟩
    have h2 : IsPGroup 2 (↥B ⧸ L₂.subgroupOf B) := fun q =>
      QuotientGroup.induction_on q fun g => by
        obtain ⟨k, hk⟩ := hpow g g.2
        refine ⟨k, ?_⟩
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        exact hk
    have htop := hB.1 (L₂.subgroupOf B) h2
    exact (Subgroup.subgroupOf_eq_top).mp htop

end Blocks

structure Data {G : Type} [Group G] [Finite G] (T M H S L : Subgroup G) (t : G) : Prop where
  cs : ConstrainedSetting G T M H S L
  alt5 : IsAltType L 5
  t_mem : t ∈ S
  ne : cj t L ≠ L
  join : conjJoin S L = L ⊔ cj t L
  comm : ⁅L, cj t L⁆ = ⊥

variable [Finite G] {T M H S L : Subgroup G}

theorem exists_data (h : A5Cfg2 G T M H S L) : ∃ t, Data T M H S L t := by
  obtain ⟨hcs, h5, hne⟩ := h
  rcases hcs.blocks with hj | ⟨t, ht, hne', hK, hcomm⟩
  · exact absurd hj hne
  · exact ⟨t, ⟨hcs, h5, ht, hne', hK, hcomm⟩⟩

omit [Finite G] in
theorem mem_SI_iff {g : G} (hg : g ∈ S) : g ∈ s2SI S L ↔ cj g L = L := by
  rw [s2SI, Subgroup.mem_inf, mem_normalizer_iff_cj]
  exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩

omit [Finite G] in
theorem cj_inj {b : G} {X Y : Subgroup G} (hXY : cj b X = cj b Y) : X = Y := by
  have := congrArg (cj b⁻¹) hXY
  rwa [cj_cj, cj_cj, inv_mul_cancel, cj_one, cj_one] at this

namespace Data

variable {t : G} (h : Data T M H S L t)
include h

theorem isShort : IsShort2 L := h.cs.block.1.1

theorem isShort₂ : IsShort2 (cj t L) := Lin2.IsShort2.map_equiv h.isShort (MulAut.conj t)

theorem alt5₂ : IsAltType (cj t L) 5 := L238.IsAltType.map_equiv h.alt5 (MulAut.conj t)

theorem comm_elem : ∀ a ∈ L, ∀ b ∈ cj t L, a * b = b * a := by
  intro a ha b hb
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h.comm
  exact (Subgroup.mem_centralizer_iff.mp (this ha) b hb).symm

theorem L_le_L₀ : L ≤ conjJoin S L := by rw [h.join]; exact le_sup_left

theorem L₂_le_L₀ : cj t L ≤ conjJoin S L := by rw [h.join]; exact le_sup_right

theorem L₂_le_normalizer : cj t L ≤ Subgroup.normalizer (L : Set G) :=
  C5.le_normalizer_of_commute fun u hu a ha => (h.comm_elem a ha u hu).symm

theorem L_le_normalizer₂ : L ≤ Subgroup.normalizer (cj t L : Set G) :=
  C5.le_normalizer_of_commute h.comm_elem

theorem L₀_le_normalizer_L : conjJoin S L ≤ Subgroup.normalizer (L : Set G) := by
  rw [h.join]; exact sup_le Subgroup.le_normalizer h.L₂_le_normalizer

theorem conj_cases {g : G} (hg : g ∈ S) : cj g L = L ∨ cj g L = cj t L := by
  have hBshort : IsShort2 (cj g L) := Lin2.IsShort2.map_equiv h.isShort (MulAut.conj g)
  have hBL₀ : cj g L ≤ L ⊔ cj t L := by
    rw [← h.join]
    exact le_iSup (fun s : S => L.map (MulAut.conj (s : G)).toMonoidHom) ⟨g, hg⟩
  have hgN : ∀ x ∈ conjJoin S L, g⁻¹ * x * g ∈ conjJoin S L := by
    intro x hx
    have hS : g⁻¹ ∈ Subgroup.normalizer (conjJoin S L : Set G) :=
      C56.S_le_normalizer_conjJoin L (S.inv_mem hg)
    have := (Subgroup.mem_normalizer_iff.mp hS x).1 hx
    simpa using this
  have hBn : L ⊔ cj t L ≤ Subgroup.normalizer (cj g L : Set G) := by
    intro x hx
    rw [← h.join] at hx
    rw [mem_normalizer_iff_cj, cj_cj]
    have hx' : g⁻¹ * x * g ∈ Subgroup.normalizer (L : Set G) := h.L₀_le_normalizer_L (hgN x hx)
    have : x * g = g * (g⁻¹ * x * g) := by group
    rw [this, ← cj_cj, mem_normalizer_iff_cj.1 hx']
  rcases le_or_le_of_normal_block h.isShort h.alt5 hBshort h.comm_elem hBL₀ hBn with hLB | hBL₂
  · left
    exact (Subgroup.eq_of_le_of_card_ge hLB (by rw [card_cj])).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge hBL₂ (by rw [card_cj, card_cj])

theorem cj_L₂_of_swap {b : G} (hb : b ∈ S) (hbL : cj b L = cj t L) : cj b (cj t L) = L := by
  rcases h.conj_cases (S.mul_mem hb h.t_mem) with h1 | h1
  · rw [cj_cj]; exact h1
  · exfalso
    rw [← cj_cj] at h1
    have : cj b (cj t L) = cj b L := by rw [h1, hbL]
    exact h.ne (cj_inj this)

theorem relIndex_SI : (s2SI S L).relIndex S = 2 := by
  show ((s2SI S L).subgroupOf S).index = 2
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨t, h.t_mem⟩, fun b => ?_⟩
  have hbt : ((b * ⟨t, h.t_mem⟩ : ↥S) : G) = (b : G) * t := rfl
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hbt, mem_SI_iff (S.mul_mem b.2 h.t_mem),
    mem_SI_iff b.2, ← cj_cj]
  rcases h.conj_cases b.2 with h1 | h1
  · right
    exact ⟨h1, fun h2 => h.ne (cj_inj (b := (b : G)) (h2.trans h1.symm))⟩
  · left
    refine ⟨h.cj_L₂_of_swap b.2 h1, fun h2 => h.ne ?_⟩
    rw [← h1, h2]

theorem SI_normal : ((s2SI S L).subgroupOf S).Normal :=
  Subgroup.normal_of_index_eq_two h.relIndex_SI

theorem cj_SI_L₂ {g : G} (hg : g ∈ s2SI S L) : cj g (cj t L) = cj t L := by
  have hgS : g ∈ S := hg.1
  have hn := h.SI_normal
  have h1 : t⁻¹ * g * t ∈ s2SI S L := by
    have := hn.conj_mem (⟨g, hgS⟩ : ↥S) (Subgroup.mem_subgroupOf.2 hg) ⟨t⁻¹, S.inv_mem h.t_mem⟩
    simpa [Subgroup.mem_subgroupOf] using Subgroup.mem_subgroupOf.1 this
  have h2 := (mem_SI_iff (S.mul_mem (S.mul_mem (S.inv_mem h.t_mem) hgS) h.t_mem)).1 h1
  have e : g * t = t * (t⁻¹ * g * t) := by group
  rw [cj_cj, e, ← cj_cj, h2]

omit [Finite G] h in
theorem cj_SI_L {g : G} (hg : g ∈ s2SI S L) : cj g L = L := (mem_SI_iff hg.1).1 hg

theorem SI_le_normalizer_L₂ : s2SI S L ≤ Subgroup.normalizer (cj t L : Set G) := fun _ hg =>
  mem_normalizer_iff_cj.2 (h.cj_SI_L₂ hg)

omit [Finite G] h in
theorem SI_le_normalizer_L : s2SI S L ≤ Subgroup.normalizer (L : Set G) := fun _ hg =>
  mem_normalizer_iff_cj.2 (cj_SI_L hg)

theorem swap_of_not_mem {g : G} (hg : g ∈ S) (hgn : g ∉ s2SI S L) :
    cj g L = cj t L ∧ cj g (cj t L) = L := by
  rcases h.conj_cases hg with h1 | h1
  · exact absurd ((mem_SI_iff hg).2 h1) hgn
  · exact ⟨h1, h.cj_L₂_of_swap hg h1⟩

end Data

end CFSG.QuasithinUnique.A5.S2
