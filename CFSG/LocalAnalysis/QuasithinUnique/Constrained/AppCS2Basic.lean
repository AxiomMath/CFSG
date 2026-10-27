module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Conj
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCSL25

public section

namespace CFSG.QuasithinUnique.AppCS2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.DoubleA3 CFSG.QuasithinUnique.A5 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

omit [Finite G] in
theorem isAltType_map_equiv {L : Subgroup G} {m : ℕ} (hL : IsAltType L m) (f : G ≃* G) :
    IsAltType (L.map f.toMonoidHom) m := by
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hβe⟩ := hL
  let φ : L ≃* (L.map f.toMonoidHom : Subgroup G) :=
    Subgroup.equivMapOfInjective L f.toMonoidHom f.injective
  have hφ : ∀ x : L, ((φ x : (L.map f.toMonoidHom : Subgroup G)) : G) = f x := fun x => rfl
  have hφsymm : ∀ y : (L.map f.toMonoidHom : Subgroup G), ((φ.symm y : L) : G) = f.symm y := by
    intro y
    apply f.injective
    rw [MulEquiv.apply_symm_apply, ← hφ, MulEquiv.apply_symm_apply]
  have hUmem : ∀ u : G, u ∈ blockU (L.map f.toMonoidHom) ↔ f.symm u ∈ blockU L := by
    intro u
    rw [Lin2.blockU_map_equiv, Subgroup.mem_map_equiv]
  have hZmem : ∀ u : G, u ∈ blockZ (L.map f.toMonoidHom) ↔ f.symm u ∈ blockZ L := by
    intro u
    rw [Lin2.blockZ_map_equiv, Subgroup.mem_map_equiv]
  let ψ : blockU (L.map f.toMonoidHom) →* blockU L :=
    MonoidHom.codRestrict (f.symm.toMonoidHom.comp (blockU (L.map f.toMonoidHom)).subtype)
      (blockU L) fun u => (hUmem u).1 u.2
  have hψ : ∀ u, ((ψ u : blockU L) : G) = f.symm (u : G) := fun u => rfl
  refine ⟨α.comp φ.symm.toMonoidHom, hαs.comp φ.symm.surjective, ?_, β.comp ψ, ?_, ?_, ?_⟩
  · ext ℓ'
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hαk,
      ← CFSG.pCore_map_iso 2 φ, Subgroup.mem_map_equiv]
    rfl
  · intro y
    obtain ⟨u, hu⟩ := hβs y
    have hfu : f (u : G) ∈ blockU (L.map f.toMonoidHom) :=
      (hUmem _).2 (by rw [MulEquiv.symm_apply_apply]; exact u.2)
    refine ⟨⟨f u, hfu⟩, ?_⟩
    have h1 : ψ ⟨f u, hfu⟩ = u := Subtype.ext (by rw [hψ]; exact MulEquiv.symm_apply_apply f _)
    rw [MonoidHom.comp_apply, h1, hu]
  · ext u'
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hβk]
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hψ]
    exact (hZmem _).symm
  · intro ℓ' u' v' h i
    have h' : ((ψ v' : blockU L) : G) = ((φ.symm ℓ' : L) : G) * ((ψ u' : blockU L) : G) *
        ((φ.symm ℓ' : L) : G)⁻¹ := by
      rw [hψ, hψ, hφsymm, h, map_mul, map_mul, InvMemClass.coe_inv, map_inv]
    exact hβe (φ.symm ℓ') (ψ u') (ψ v') h' i

omit [Finite G] in
theorem isAltType_conjR {L : Subgroup G} {m : ℕ} (hL : IsAltType L m) (g : G) :
    IsAltType (conjR L g) m :=
  isAltType_map_equiv hL (MulAut.conj g⁻¹)

omit [Finite G] in
theorem normal_le_or_eq_alt5 {L : Subgroup G} (hL : IsShort2 L) (h5 : IsAltType L 5)
    {W : Subgroup G} (hWL : W ≤ L) (hn : ∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W) :
    W ≤ blockQ L ∨ W = L := by
  classical
  obtain ⟨α, hα, hαk, -⟩ := h5
  set W' : Subgroup ↥L := W.subgroupOf L with hW'
  have hnorm : W'.Normal := ⟨fun w hw g => by
    rw [hW', Subgroup.mem_subgroupOf] at hw ⊢
    show ((g * w * g⁻¹ : ↥L) : G) ∈ W
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hn _ g.2 _ hw⟩
  have hmapn : (W'.map α).Normal := Subgroup.Normal.map hnorm α hα
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (α := Fin 5) (by simp) (N := W'.map α)
    with h | h
  · left
    intro w hw
    have hwL : w ∈ L := hWL hw
    have h1 : α ⟨w, hwL⟩ = 1 := by
      have : α ⟨w, hwL⟩ ∈ W'.map α := ⟨⟨w, hwL⟩, Subgroup.mem_subgroupOf.2 hw, rfl⟩
      rw [h] at this
      exact Subgroup.mem_bot.1 this
    have h2 : (⟨w, hwL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
      rw [← hαk]; exact h1
    exact (mem_pCore_iff_mem_blockQ _).1 h2
  · right
    refine le_antisymm hWL fun l hl => ?_
    have hP2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
    have hq : IsPGroup 2 (↥L ⧸ W') := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have : α g ∈ W'.map α := by rw [h]; trivial
      obtain ⟨w, hw, hwg⟩ := this
      have hp : (w⁻¹ * g) ∈ α.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hwg, inv_mul_cancel]
      rw [hαk] at hp
      obtain ⟨k, hk⟩ := hP2 ⟨w⁻¹ * g, hp⟩
      refine ⟨k, ?_⟩
      have hk' : (w⁻¹ * g) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
      have hq1 : (QuotientGroup.mk (w⁻¹ * g) : ↥L ⧸ W') = QuotientGroup.mk g := by
        rw [QuotientGroup.eq]
        have := hnorm.conj_mem w hw g⁻¹
        simpa [mul_assoc] using this
      rw [← hq1, ← QuotientGroup.mk_pow, hk']
      rfl
    have htop := hL.1 W' hq
    have : (⟨l, hl⟩ : ↥L) ∈ W' := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.1 this

omit [Finite G] in
theorem mem_blockQ_of_comm_alt5 {L : Subgroup G} (h5 : IsAltType L 5) {a : G} (ha : a ∈ L)
    (h : ∀ y ∈ L, a * y * a⁻¹ * y⁻¹ ∈ blockQ L) : a ∈ blockQ L := by
  classical
  obtain ⟨α, hα, hαk, -⟩ := h5
  have hc : α ⟨a, ha⟩ ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := hα z
    have hy : y.1 ∈ L := y.2
    have h1 := h y hy
    have h2 : (⟨a * y * a⁻¹ * y⁻¹, mul_mem (mul_mem (mul_mem ha hy) (inv_mem ha)) (inv_mem hy)⟩ :
        ↥L) ∈ CFSG.pCore 2 ↥L := (mem_pCore_iff_mem_blockQ _).2 h1
    rw [← hαk, MonoidHom.mem_ker] at h2
    have h3 : α ⟨a, ha⟩ * α y * (α ⟨a, ha⟩)⁻¹ * (α y)⁻¹ = 1 := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact h2
    calc α y * α ⟨a, ha⟩ = (α ⟨a, ha⟩ * α y * (α ⟨a, ha⟩)⁻¹ * (α y)⁻¹) * (α y * α ⟨a, ha⟩) := by
          rw [h3, one_mul]
      _ = α ⟨a, ha⟩ * α y := by group
  rw [alternatingGroup.center_eq_bot (α := Fin 5) (by simp)] at hc
  have h1 : α ⟨a, ha⟩ = 1 := Subgroup.mem_bot.1 hc
  have h2 : (⟨a, ha⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by rw [← hαk]; exact h1
  exact (mem_pCore_iff_mem_blockQ _).1 h2

omit [Finite G] in
theorem three_dvd_card_of_alt5 {L : Subgroup G} (h5 : IsAltType L 5) : 3 ∣ Nat.card ↥L := by
  obtain ⟨α, hα, -, -⟩ := h5
  have h60 : Nat.card (alternatingGroup (Fin 5)) ∣ Nat.card ↥L := Subgroup.card_dvd_of_surjective hα
  rw [card_alt5] at h60
  exact (by norm_num : 3 ∣ 60).trans h60

structure Dbl (T M H S L : Subgroup G) (t : G) : Prop where
  hcs : ConstrainedSetting G T M H S L
  h5 : IsAltType L 5
  ht : t ∈ S
  hne : conjR L t ≠ L
  hjoin : conjJoin S L = L ⊔ conjR L t
  hcomm : ⁅L, conjR L t⁆ = ⊥

theorem exists_dbl (hcs : ConstrainedSetting G T M H S L) (h5 : IsAltType L 5)
    (hne : conjJoin S L ≠ L) : ∃ t : G, Nonempty (Dbl T M H S L t) := by
  rcases hcs.blocks with h | ⟨t, ht, hne', hjoin, hcomm⟩
  · exact absurd h hne
  · refine ⟨t⁻¹, ⟨⟨hcs, h5, S.inv_mem ht, ?_, ?_, ?_⟩⟩⟩
    · intro h
      apply hne'
      have : conjR L t⁻¹ = L.map (MulAut.conj t).toMonoidHom := by
        simp [conjR]
      rw [← this]; exact h
    · have : conjR L t⁻¹ = L.map (MulAut.conj t).toMonoidHom := by simp [conjR]
      rw [this]; exact hjoin
    · have : conjR L t⁻¹ = L.map (MulAut.conj t).toMonoidHom := by simp [conjR]
      rw [this]; exact hcomm

namespace Dbl

variable {t : G} (D : Dbl T M H S L t)
include D

theorem hL : IsShort2 L := C56.isShort D.hcs

theorem hL₂ : IsShort2 (conjR L t) := (Lin2.isShort2_conjR_iff L t).2 D.hL

theorem h5₂ : IsAltType (conjR L t) 5 := isAltType_conjR D.h5 t

theorem comm_elem : ∀ a ∈ L, ∀ b ∈ conjR L t, a * b = b * a := by
  intro a ha b hb
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp D.hcomm
  exact (Subgroup.mem_centralizer_iff.mp (this ha) b hb).symm

theorem L₂_le_K : conjR L t ≤ conjJoin S L := conjR_le_conjJoin' D.ht

theorem K_le_N_L : conjJoin S L ≤ normalizer (L : Set G) := by
  rw [D.hjoin]
  exact sup_le Subgroup.le_normalizer
    (C5.le_normalizer_of_commute (fun u hu a ha => (D.comm_elem a ha u hu).symm))

theorem K_le_N_conjR {g : G} (hg : g ∈ S) :
    conjJoin S L ≤ normalizer ((conjR L g : Subgroup G) : Set G) := by
  have h1 := C5.conjSubgroup_mono D.K_le_N_L g
  rw [C5.conjSubgroup_normalizer, C5.conjSubgroup_eq_self (C56.S_le_normalizer_conjJoin L hg)]
    at h1
  exact h1

theorem conjR_cases {g : G} (hg : g ∈ S) : conjR L g = L ∨ conjR L g = conjR L t := by
  classical
  set L₂ := conjR L t with hL₂def
  set N := conjR L g with hNdef
  have hLs := D.hL
  have hN5 : IsAltType N 5 := isAltType_conjR D.h5 g
  have hNK : N ≤ conjJoin S L := conjR_le_conjJoin' hg
  have hNn : conjJoin S L ≤ normalizer (N : Set G) := D.K_le_N_conjR hg
  have hLK : L ≤ conjJoin S L := C56.le_conjJoin L S.one_mem
  have hL₂K := D.L₂_le_K
  have hcard : Nat.card ↥N = Nat.card ↥L := C5.card_conjSubgroup L g
  have hnL : ∀ l ∈ L, ∀ w ∈ N ⊓ L, l * w * l⁻¹ ∈ N ⊓ L := by
    intro l hl w hw
    have h1 : l * w * l⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.1 (hNn (hLK hl)) w).1 hw.1
    have h2 : l * w * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hw.2) (L.inv_mem hl)
    exact ⟨h1, h2⟩
  have hnL₂ : ∀ l ∈ L₂, ∀ w ∈ N ⊓ L₂, l * w * l⁻¹ ∈ N ⊓ L₂ := by
    intro l hl w hw
    have h1 : l * w * l⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.1 (hNn (hL₂K hl)) w).1 hw.1
    have h2 : l * w * l⁻¹ ∈ L₂ := L₂.mul_mem (L₂.mul_mem hl hw.2) (L₂.inv_mem hl)
    exact ⟨h1, h2⟩
  have h1 := normal_le_or_eq_alt5 D.hL D.h5 (inf_le_right : N ⊓ L ≤ L) hnL
  have h2 := normal_le_or_eq_alt5 D.hL₂ D.h5₂ (inf_le_right : N ⊓ L₂ ≤ L₂) hnL₂
  rcases h1 with h1 | h1
  swap
  ·
    left
    have hLN : L ≤ N := by rw [← h1]; exact inf_le_left
    exact (Subgroup.eq_of_le_of_card_ge hLN hcard.le).symm
  rcases h2 with h2 | h2
  swap
  · right
    have hLN : L₂ ≤ N := by rw [hL₂def, ← h2]; exact inf_le_left
    have hc2 : Nat.card ↥L₂ = Nat.card ↥L := C5.card_conjSubgroup L t
    exact (Subgroup.eq_of_le_of_card_ge hLN (by rw [hcard, hc2])).symm
  exfalso
  have hcommLL : ∀ a ∈ L, ∀ b ∈ L₂, a * b = b * a := D.comm_elem
  have hLN : L ≤ normalizer (L₂ : Set G) :=
    C5.le_normalizer_of_commute (fun u hu a ha => D.comm_elem u hu a ha)
  have hpow : ∀ x ∈ N, ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
    intro x hx
    have hxK : x ∈ conjJoin S L := hNK hx
    rw [D.hjoin] at hxK
    have hxK' : x ∈ ((L ⊔ L₂ : Subgroup G) : Set G) := hxK
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L L₂ hLN] at hxK'
    obtain ⟨a, ha, b, hb, hab⟩ := hxK'
    have hab' : a * b = x := hab
    have haQ : a ∈ blockQ L := by
      refine mem_blockQ_of_comm_alt5 D.h5 ha fun y hy => ?_
      have hby : b * y = y * b := (hcommLL y hy b hb).symm
      have e : x * y * x⁻¹ * y⁻¹ = a * y * a⁻¹ * y⁻¹ := by
        rw [← hab']
        calc a * b * y * (a * b)⁻¹ * y⁻¹ = a * (b * y) * b⁻¹ * a⁻¹ * y⁻¹ := by group
          _ = a * (y * b) * b⁻¹ * a⁻¹ * y⁻¹ := by rw [hby]
          _ = a * y * a⁻¹ * y⁻¹ := by group
      have hmem : x * y * x⁻¹ * y⁻¹ ∈ N := by
        have h3 : y * x⁻¹ * y⁻¹ ∈ N :=
          (Subgroup.mem_normalizer_iff.1 (hNn (hLK hy)) x⁻¹).1 (inv_mem hx)
        have : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
        rw [this]
        exact mul_mem hx h3
      have hmemL : a * y * a⁻¹ * y⁻¹ ∈ L :=
        mul_mem (mul_mem (mul_mem ha hy) (inv_mem ha)) (inv_mem hy)
      rw [e] at hmem
      exact h1 ⟨hmem, hmemL⟩
    have hbQ : b ∈ blockQ L₂ := by
      refine mem_blockQ_of_comm_alt5 D.h5₂ hb fun y hy => ?_
      have hay : a * (b * y * b⁻¹) = (b * y * b⁻¹) * a :=
        hcommLL a ha _ (mul_mem (mul_mem hb hy) (inv_mem hb))
      have e : x * y * x⁻¹ * y⁻¹ = b * y * b⁻¹ * y⁻¹ := by
        rw [← hab']
        calc a * b * y * (a * b)⁻¹ * y⁻¹ = a * (b * y * b⁻¹) * a⁻¹ * y⁻¹ := by group
          _ = (b * y * b⁻¹) * a * a⁻¹ * y⁻¹ := by rw [hay]
          _ = b * y * b⁻¹ * y⁻¹ := by group
      have hmem : x * y * x⁻¹ * y⁻¹ ∈ N := by
        have h3 : y * x⁻¹ * y⁻¹ ∈ N :=
          (Subgroup.mem_normalizer_iff.1 (hNn (hL₂K hy)) x⁻¹).1 (inv_mem hx)
        have : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
        rw [this]
        exact mul_mem hx h3
      have hmemL : b * y * b⁻¹ * y⁻¹ ∈ L₂ :=
        mul_mem (mul_mem (mul_mem hb hy) (inv_mem hb)) (inv_mem hy)
      rw [e] at hmem
      exact h2 ⟨hmem, hmemL⟩
    obtain ⟨k₁, hk₁⟩ := C1.blockQ_isPGroup L ⟨a, haQ⟩
    obtain ⟨k₂, hk₂⟩ := C1.blockQ_isPGroup L₂ ⟨b, hbQ⟩
    have hk₁' : a ^ (2 ^ k₁) = 1 := congrArg Subtype.val hk₁
    have hk₂' : b ^ (2 ^ k₂) = 1 := congrArg Subtype.val hk₂
    refine ⟨k₁ + k₂, ?_⟩
    rw [← hab', (show Commute a b from hcommLL a ha b hb).mul_pow, pow_add, pow_mul, pow_mul', hk₁', hk₂']
    simp
  have hN2 : IsPGroup 2 ↥N := by
    intro g
    obtain ⟨k, hk⟩ := hpow g.1 g.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hN2
  have h3 := three_dvd_card_of_alt5 D.h5
  rw [← hcard, hn] at h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

omit [Finite G] D in
theorem mem_normalizer_iff_conjR {g : G} : g ∈ normalizer (L : Set G) ↔ conjR L g = L :=
  conjSubgroup_eq_iff_mem_normalizer.symm

theorem conjR_eq_t_of_not_mem {g : G} (hg : g ∈ S) (hn : g ∉ normalizer (L : Set G)) :
    conjR L g = conjR L t := by
  rcases D.conjR_cases hg with h | h
  · exact absurd (mem_normalizer_iff_conjR.2 h) hn
  · exact h

omit [Finite G] D in
theorem conjR_conjR (X : Subgroup G) (g h : G) : conjR (conjR X g) h = conjR X (g * h) :=
  conjSubgroup_conjSubgroup X g h

omit [Finite G] D in
theorem conjR_conjR_inv (X : Subgroup G) (g : G) : conjR (conjR X g) g⁻¹ = X := by
  rw [conjR_conjR, mul_inv_cancel]
  exact conjSubgroup_one _

theorem conjR_L₂_cases {g : G} (hg : g ∈ S) :
    (conjR L g = L ∧ conjR (conjR L t) g = conjR L t) ∨
      (conjR L g = conjR L t ∧ conjR (conjR L t) g = L) := by
  have hne := D.hne
  have h2 : conjR (conjR L t) g = conjR L (t * g) := conjR_conjR L t g
  have htg : t * g ∈ S := S.mul_mem D.ht hg
  have hid : conjR (conjR L g) g⁻¹ = L := conjR_conjR_inv L g
  have hid2 : conjR (conjR (conjR L t) g) g⁻¹ = conjR L t := conjR_conjR_inv (conjR L t) g
  rcases D.conjR_cases hg with h | h
  · left
    refine ⟨h, ?_⟩
    rcases D.conjR_cases htg with h' | h'
    · exfalso
      apply hne
      rw [h2, h'] at hid2
      rw [h] at hid
      exact hid2.symm.trans hid
    · rw [h2]; exact h'
  · right
    refine ⟨h, ?_⟩
    rcases D.conjR_cases htg with h' | h'
    · rw [h2]; exact h'
    · exfalso
      apply hne
      have h5 : conjR (conjR L t) g = conjR L t := by rw [h2]; exact h'
      rw [h5, ← h] at hid2
      exact h.symm.trans (hid2.symm.trans hid)

theorem s2SI_le_normalizer_L₂ : s2SI S L ≤ normalizer ((conjR L t : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_conjR]
  have hgN : conjR L g = L := mem_normalizer_iff_conjR.1 hg.2
  rcases D.conjR_L₂_cases hg.1 with h | h
  · exact h.2
  · exact absurd hgN (by rw [h.1]; exact D.hne)

theorem thompsonJ_le_s2SI : thompsonJ S ≤ s2SI S L :=
  fun _ hy => ⟨GammaExtra.thompsonJ_le_self S hy, C56.le_normalizer_of_commutator_eq D.hcs.thompson hy⟩

theorem blockU_inf_blockU₂ : blockU L ⊓ conjR (blockU L) t = ⊥ := by
  refine eq_bot_iff.2 fun u hu => ?_
  have hu₂ : u ∈ conjR L t := by
    have : u ∈ blockU (conjR L t) := by rw [blockU_conjR]; exact hu.2
    exact C1.blockQ_le _ (C1.blockU_le_blockQ D.hL₂ this)
  have hZ : u ∈ blockZ L := ⟨hu.1, Subgroup.mem_centralizer_iff.2 fun l hl =>
    D.comm_elem l hl u hu₂⟩
  rw [blockZ_eq_bot_of_alt5 D.hL D.h5] at hZ
  exact hZ

theorem s2SI_normal {g s : G} (hg : g ∈ S) (hs : s ∈ s2SI S L) : g * s * g⁻¹ ∈ s2SI S L := by
  have hgsS : g * s * g⁻¹ ∈ S := S.mul_mem (S.mul_mem hg hs.1) (S.inv_mem hg)
  refine ⟨hgsS, ?_⟩
  show g * s * g⁻¹ ∈ normalizer (L : Set G)
  rw [mem_normalizer_iff_conjR]
  have hsN : conjR L s = L := mem_normalizer_iff_conjR.1 hs.2
  have hsN₂ : conjR (conjR L t) s = conjR L t :=
    mem_normalizer_iff_conjR.1 (D.s2SI_le_normalizer_L₂ hs)
  have e : conjR L (g * s * g⁻¹) = conjR (conjR (conjR L g) s) g⁻¹ := by
    rw [conjR_conjR, conjR_conjR, mul_assoc]
  have hid : conjR (conjR L g) g⁻¹ = L := conjR_conjR_inv L g
  rw [e]
  rcases D.conjR_cases hg with h | h
  · rw [h, hsN]
    rw [h] at hid
    exact hid
  · rw [h, hsN₂]
    rw [h] at hid
    exact hid

end Dbl

end CFSG.QuasithinUnique.AppCS2
