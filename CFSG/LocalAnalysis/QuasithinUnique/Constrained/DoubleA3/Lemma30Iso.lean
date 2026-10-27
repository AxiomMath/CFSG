module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma30Five
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalKleinFourIndexThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.AutAlternatingFour

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem IsA4Block.nonempty_mulEquiv [Finite G] {L U : Subgroup G} (h : IsA4Block L U) :
    Nonempty (↥L ≃* alternatingGroup (Fin 4)) := by
  have hUL : U ≤ L := h.le
  obtain ⟨c, -, -, hcN, -, hLc⟩ := h.exists_c
  have hLN : L ≤ normalizer (U : Set G) := by
    rw [hLc]; exact sup_le Subgroup.le_normalizer (zpowers_le.mpr hcN)
  have hcard : Nat.card ↥(U.subgroupOf L) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUL).toEquiv]
    exact h.card_U
  have hnormal : (U.subgroupOf L).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hUL).mpr fun u k hu hk => ?_
    exact (Subgroup.mem_normalizer_iff.mp (hLN hk) u).mp hu
  have hKlein : IsKleinFour ↥(U.subgroupOf L) := by
    have hnt : Nontrivial ↥(U.subgroupOf L) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcard]
      norm_num
    refine ⟨hcard, ?_⟩
    rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro g hg
    refine orderOf_eq_prime ?_ hg
    apply Subtype.ext
    apply Subtype.ext
    simpa using h.sq_U (((g : ↥L)) : G) g.2
  have hcentr : centralizer ((U.subgroupOf L : Subgroup ↥L) : Set ↥L) = U.subgroupOf L := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff] at hx
      refine Subgroup.mem_subgroupOf.mpr (h.mem_of_centralizes x.2 fun u hu => ?_)
      have := hx ⟨u, hUL hu⟩ (Subgroup.mem_subgroupOf.mpr hu)
      exact (congrArg Subtype.val this).symm
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subtype.ext
        (h.comm_U _ (Subgroup.mem_subgroupOf.mp hy) _ (Subgroup.mem_subgroupOf.mp hx))
  have hindex : (U.subgroupOf L).index = 3 := by
    have := (U.subgroupOf L).card_mul_index
    rw [hcard, h.card_L] at this
    omega
  exact CFSG.GorensteinWalter.mulEquiv_alternatingGroup_four_of_normal_kleinFour_index_three
    _ hnormal hKlein hcentr hindex

theorem IsA4Block.exists_act [Finite G] {L U Y : Subgroup G} (h : IsA4Block L U)
    (hY : Y ≤ normalizer (L : Set G)) :
    ∃ f : ↥Y →* Equiv.Perm (Fin 4), ∀ y : ↥Y, f y = 1 → ∀ l ∈ L, (y : G) * l = l * (y : G) := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj
  let φ : ↥Y →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hY)
  let ψ : MulAut ↥L ≃* MulAut (alternatingGroup (Fin 4)) := MulAut.congr e
  let χ : MulAut (alternatingGroup (Fin 4)) ≃* Equiv.Perm (Fin 4) :=
    (MulEquiv.ofBijective _ hbij).symm
  refine ⟨χ.toMonoidHom.comp (ψ.toMonoidHom.comp φ), fun y hy l hl => ?_⟩
  have h1 : ψ (φ y) = 1 := by
    apply χ.injective
    simpa using hy
  have h2 : φ y = 1 := ψ.injective (by simpa using h1)
  have h3 := congrArg (fun a : MulAut ↥L => ((a ⟨l, hl⟩ : ↥L) : G)) h2
  simp [φ] at h3
  calc (y : G) * l = ((y : G) * l * (y : G)⁻¹) * (y : G) := by group
    _ = l * (y : G) := by rw [h3]

theorem kernel_trivial_of_sylow [Finite G] {Y L₀ Y₀ S : Subgroup G}
    (hL₀Y : L₀ ≤ Y) (hYN : Y ≤ normalizer (L₀ : Set G))
    (hcenter : ∀ g ∈ L₀, (∀ l ∈ L₀, g * l = l * g) → g = 1)
    (hcardY : Nat.card Y = 576) (hcardL₀ : Nat.card L₀ = 144)
    (hsyl : IsSylowTwoOf Y₀ Y) (hY₀S : Y₀ ≤ S)
    (hDY : (S ⊓ centralizer (L₀ : Set G)) ⊓ Y = ⊥) :
    ∀ y ∈ Y, (∀ l ∈ L₀, y * l = l * y) → y = 1 := by
  intro y hyY hyc
  set C : Subgroup G := Y ⊓ centralizer (L₀ : Set G) with hC
  have hyC : y ∈ C := ⟨hyY, Subgroup.mem_centralizer_iff.mpr fun l hl => (hyc l hl).symm⟩
  have hCL₀ : C ⊓ L₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨⟨-, hgC⟩, hgL⟩
    have := hcenter g hgL fun l hl => (Subgroup.mem_centralizer_iff.mp hgC l hl).symm
    rw [this]; exact one_mem _
  have hCN : C ≤ normalizer (L₀ : Set G) := C5.le_normalizer_of_commute fun c hc a ha =>
    (Subgroup.mem_centralizer_iff.mp hc.2 a ha).symm
  have hmul := C5.card_sup_mul_card_inf_of_le_normalizer hCN
  rw [hCL₀, Subgroup.card_bot, mul_one, hcardL₀] at hmul
  have hCLY : C ⊔ L₀ ≤ Y := sup_le inf_le_left hL₀Y
  have hdvd : Nat.card ↥(C ⊔ L₀) ∣ Nat.card Y := Subgroup.card_dvd_of_le hCLY
  rw [hmul, hcardY] at hdvd
  have hC4 : Nat.card ↥C ∣ 4 := by
    have : Nat.card ↥C * 144 ∣ 4 * 144 := by simpa using hdvd
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
  have hC2 : IsPGroup 2 ↥C := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 2) (i := Nat.card ↥C)).mp
      (by simpa using hC4)
    exact IsPGroup.of_card hm
  have hCYN : Y ≤ normalizer (C : Set G) := fun g hg =>
    C5.mem_normalizer_inf (Subgroup.le_normalizer hg) (C5.mem_normalizer_centralizer (hYN hg))
  have hCY0 : C ≤ Y₀ := hsyl.le_of_normalizes inf_le_left hCYN hC2
  have hCD : C ≤ (S ⊓ centralizer (L₀ : Set G)) ⊓ Y :=
    le_inf (le_inf (hCY0.trans hY₀S) inf_le_right) inf_le_left
  rw [hDY] at hCD
  exact Subgroup.mem_bot.mp (hCD hyC)

theorem card_Y_aux [Finite G] {D U0 U0x L₀ Q R : Subgroup G}
    (hR : R = D ⊔ (U0 ⊔ U0x)) (hQ : Q = D ⊔ U0)
    (hDY₀ : D ⊓ (U0 ⊔ U0x) = ⊥)
    (hDc : ∀ d ∈ D, ∀ y ∈ U0 ⊔ U0x, d * y = y * d)
    (hRQ : Nat.card R = 4 * Nat.card Q)
    (hU0N : U0x ≤ normalizer (U0 : Set G))
    (hcardU0 : Nat.card U0 = 16) (hcardU0x : Nat.card U0x = 16)
    (hcardL₀ : Nat.card L₀ = 144) (hU0xL₀N : U0x ≤ normalizer (L₀ : Set G))
    (hIL : U0x ⊓ L₀ = U0x ⊓ U0) :
    Nat.card ↥(U0 ⊔ U0x) = 64 ∧ Nat.card ↥(L₀ ⊔ U0x) = 576 := by
  have hDN : D ≤ normalizer ((U0 ⊔ U0x : Subgroup G) : Set G) :=
    C5.le_normalizer_of_commute fun d hd y hy => hDc d hd y hy
  have h1 := C5.card_sup_mul_card_inf_of_le_normalizer hDN
  rw [hDY₀, Subgroup.card_bot, mul_one, ← hR] at h1
  have hDN2 : D ≤ normalizer (U0 : Set G) :=
    C5.le_normalizer_of_commute fun d hd u hu => hDc d hd u (mem_sup_left hu)
  have h2 := C5.card_sup_mul_card_inf_of_le_normalizer hDN2
  have hDU0 : D ⊓ U0 = ⊥ := by
    rw [eq_bot_iff, ← hDY₀]
    exact inf_le_inf_left D le_sup_left
  rw [hDU0, Subgroup.card_bot, mul_one, ← hQ] at h2
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have h3 : Nat.card ↥(U0 ⊔ U0x) = 64 := by
    have : Nat.card D * Nat.card ↥(U0 ⊔ U0x) = Nat.card D * 64 := by
      rw [← h1, hRQ, h2, hcardU0]; ring
    exact Nat.eq_of_mul_eq_mul_left hDpos this
  refine ⟨h3, ?_⟩
  have h4 := C5.card_sup_mul_card_inf_of_le_normalizer hU0N
  rw [sup_comm, h3, hcardU0x, hcardU0] at h4
  have hI : Nat.card ↥(U0x ⊓ U0) = 4 := by omega
  have h5 := C5.card_sup_mul_card_inf_of_le_normalizer hU0xL₀N
  rw [sup_comm, hIL, hI, hcardU0x, hcardL₀] at h5
  omega

theorem iso_of_two_actions [Finite G] {Y : Subgroup G}
    (f₁ f₂ : ↥Y →* Equiv.Perm (Fin 4))
    (hker : ∀ y : ↥Y, f₁ y = 1 → f₂ y = 1 → y = 1) (hcard : Nat.card Y = 576) :
    Nonempty (↥Y ≃* (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4))) := by
  let Φ : ↥Y →* Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) := f₁.prod f₂
  have hinj : Function.Injective Φ := (injective_iff_map_eq_one Φ).mpr fun y hy =>
    hker y (congrArg Prod.fst hy) (congrArg Prod.snd hy)
  have hcardP : Nat.card (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)) = 576 := by
    rw [Nat.card_prod, Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  have hbij : Function.Bijective Φ :=
    (Nat.bijective_iff_injective_and_card Φ).mpr ⟨hinj, by rw [hcard, hcardP]⟩
  exact ⟨MulEquiv.ofBijective Φ hbij⟩

namespace A3A3

variable [Finite G] {T M H S L : Subgroup G} {s : G}

theorem card_L0 (h : A3A3 T M H S L s) : Nat.card ↥(conjJoin S L) = 144 := by
  rw [h.join]
  have := C5.card_sup_mul_card_inf_of_le_normalizer (C5.le_normalizer_of_commute h.comm_elem)
  rw [h.inf_Ls, Subgroup.card_bot, mul_one, h.isA4.card_L, h.isA4s.card_L] at this
  omega

theorem card_V (h : A3A3 T M H S L s) : Nat.card ↥(blockU L ⊔ blockU2 L s) = 16 := by
  have hUU : ∀ a ∈ blockU L, ∀ b ∈ blockU2 L s, a * b = b * a := fun a ha b hb =>
    h.comm_elem a (h.isA4.le ha) b (h.isA4s.le hb)
  have hUN : blockU L ≤ normalizer (blockU2 L s : Set G) := C5.le_normalizer_of_commute hUU
  have hbot : blockU L ⊓ blockU2 L s = ⊥ :=
    le_bot_iff.mp ((inf_le_inf h.isA4.le h.isA4s.le).trans (le_of_eq h.inf_Ls))
  have := C5.card_sup_mul_card_inf_of_le_normalizer hUN
  rw [hbot, Subgroup.card_bot, mul_one, h.isA4.card_U, h.isA4s.card_U] at this
  omega

end A3A3

theorem lemma2_4_30_iso (hD : AppC.C56DoubleA3)
    (h27_1 : Lemma2_4_27_1A3) : Lemma2_4_30Iso := by
  intro G _ _ T M H S L s hcfg x hxT hxS
  have hcs := hcfg.cs
  have h3 := hcfg.a3
  have hne : conjJoin S L ≠ L := hcfg.conjJoin_ne
  obtain ⟨hidx, -, -⟩ := h27_1 G T M H S L hcs h3 hne
  have hTN : T ≤ normalizer (S : Set G) := normalizer_of_relIndex_two hcs.le_T hidx
  obtain ⟨hU0, -, hbD, hQ, -, -, hx⟩ := hD G T M H S L hcs h3 hne T hcs.le_T le_rfl hidx
  have hQ' : pCoreOf 2 H = blockD S L ⊔ blockU0 S L := by rw [← hbD]; exact hQ
  obtain ⟨-, hbaum, -⟩ := hx x hxT hxS
  have hbaumeq : baum S = blockD S L ⊔ (blockU0 S L ⊔ conjR (blockU0 S L) x) := by
    have h1 : baum S = baumD S L ⊔ (blockU0 S L ⊔ conjR (blockU0 S L) x) :=
      hbaum.trans (sup_assoc _ _ _)
    rw [hbD] at h1
    exact h1
  have hinf := blockD_inf_sup_conj hD hcfg hU0 hQ' hcs.le_T le_rfl hidx hxT hxS
  obtain ⟨-, hRQ⟩ := normalizer_eq_baum hD hcfg hU0 hbD hQ' hidx
  obtain ⟨-, hDY, -⟩ := lemma2_4_30_four hD h27_1 hcfg x hxT hxS
  have hA := hcfg.isA4
  have hAs := hcfg.isA4s
  have hUL : blockU L ≤ L := hA.le
  have hU0L : blockU0 S L ≤ conjJoin S L := iSup_mono fun g => Subgroup.map_mono hUL
  have hU0S : blockU0 S L ≤ S :=
    (by rw [hQ']; exact le_sup_right : blockU0 S L ≤ pCoreOf 2 H).trans hcs.sylow.pCoreOf_le
  have hU0xS : conjR (blockU0 S L) x ≤ S :=
    (C5.conjSubgroup_mono hU0S x).trans (le_of_eq (C5.conjSubgroup_eq_self (hTN hxT)))
  have hSL0 : S ≤ normalizer (conjJoin S L : Set G) := C56.S_le_normalizer_conjJoin L
  have hSU0 : S ≤ normalizer (blockU0 S L : Set G) := C56.S_le_normalizer_conjJoin (blockU L)
  have hcardU0 : Nat.card ↥(blockU0 S L) = 16 := by
    rw [hcfg.blockU0_eq hU0]; exact hcfg.card_V
  have hcardU0x : Nat.card ↥(conjR (blockU0 S L) x) = 16 := by
    rw [← hcardU0]; exact C5.card_conjSubgroup (blockU0 S L) x
  have hIL : conjR (blockU0 S L) x ⊓ conjJoin S L = conjR (blockU0 S L) x ⊓ blockU0 S L := by
    refine le_antisymm (fun g hg => ?_) (inf_le_inf_left _ hU0L)
    have hgS : g ∈ S ⊓ conjJoin S L := ⟨hU0xS hg.1, hg.2⟩
    rw [hcfg.inf_S_L0 hU0 hU0S] at hgS
    exact ⟨hg.1, hgS⟩
  obtain ⟨hcardY₀, hcardY⟩ := card_Y_aux hbaumeq hQ' hinf.1 hinf.2 hRQ (hU0xS.trans hSU0)
    hcardU0 hcardU0x hcfg.card_L0 (hU0xS.trans hSL0) hIL
  have hY₀Y : blockU0 S L ⊔ conjR (blockU0 S L) x ≤ conjJoin S L ⊔ conjR (blockU0 S L) x :=
    sup_le (hU0L.trans le_sup_left) le_sup_right
  have hY₀S : blockU0 S L ⊔ conjR (blockU0 S L) x ≤ S := sup_le hU0S hU0xS
  have hsyl : IsSylowTwoOf (blockU0 S L ⊔ conjR (blockU0 S L) x)
      (conjJoin S L ⊔ conjR (blockU0 S L) x) := by
    refine ⟨hY₀Y, hcs.sylow.isPGroup.to_le hY₀S, ?_⟩
    have hrel := C5.card_eq_card_mul_relIndex hY₀Y
    rw [hcardY, hcardY₀] at hrel
    have hr : (blockU0 S L ⊔ conjR (blockU0 S L) x).relIndex
        (conjJoin S L ⊔ conjR (blockU0 S L) x) = 9 := by omega
    show ¬ 2 ∣ (blockU0 S L ⊔ conjR (blockU0 S L) x).relIndex
      (conjJoin S L ⊔ conjR (blockU0 S L) x)
    rw [hr]; omega
  have hYN : conjJoin S L ⊔ conjR (blockU0 S L) x ≤ normalizer (conjJoin S L : Set G) :=
    sup_le Subgroup.le_normalizer (hU0xS.trans hSL0)
  have hker := kernel_trivial_of_sylow (le_sup_left :
    conjJoin S L ≤ conjJoin S L ⊔ conjR (blockU0 S L) x) hYN hcfg.center_L0 hcardY
    hcfg.card_L0 hsyl hY₀S hDY
  obtain ⟨hBL, -⟩ := (C56.baumann_A3_cs hcs h3).2
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hcfg.s_mem
  have hBLs : baum S ≤ normalizer (conjR L s : Set G) := C5.le_normalizer_conj hsB hBL
  have hU0xB : conjR (blockU0 S L) x ≤ baum S := by
    rw [hbaumeq]
    exact (le_sup_right : _ ≤ blockU0 S L ⊔ conjR (blockU0 S L) x).trans le_sup_right
  have hL₀L : conjJoin S L ≤ normalizer (L : Set G) := by
    rw [hcfg.join]
    exact sup_le Subgroup.le_normalizer
      (C5.le_normalizer_of_commute fun u hu a ha => (hcfg.comm_elem a ha u hu).symm)
  have hL₀Ls : conjJoin S L ≤ normalizer (conjR L s : Set G) :=
    hcfg.normalizer_conjR hcfg.s_mem
  obtain ⟨f₁, hf₁⟩ := hA.exists_act (sup_le hL₀L (hU0xB.trans hBL))
  obtain ⟨f₂, hf₂⟩ := hAs.exists_act (sup_le hL₀Ls (hU0xB.trans hBLs))
  refine iso_of_two_actions f₁ f₂ (fun y h1 h2 => ?_) hcardY
  have hcL := hf₁ y h1
  have hcLs := hf₂ y h2
  have hyc : ∀ l ∈ conjJoin S L, (y : G) * l = l * (y : G) := by
    intro l hl
    rw [hcfg.join] at hl
    have hle : L ⊔ conjR L s ≤ centralizer ({(y : G)} : Set G) := by
      refine sup_le (fun l hl => ?_) (fun l hl => ?_)
      · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
        rw [Set.mem_singleton_iff] at hh
        rw [hh]; exact hcL l hl
      · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
        rw [Set.mem_singleton_iff] at hh
        rw [hh]; exact hcLs l hl
    exact Subgroup.mem_centralizer_iff.mp (hle hl) (y : G) (Set.mem_singleton _)
  exact Subtype.ext (hker y y.2 hyc)

theorem lemma2_4_30 (hD : AppC.C56DoubleA3)
    (h27_1 : Lemma2_4_27_1A3) : Lemma2_4_30 :=
  lemma2_4_30_of_iso hD h27_1 (lemma2_4_30_iso hD h27_1)

end CFSG.QuasithinUnique.DoubleA3
