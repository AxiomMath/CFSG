module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup

open CFSG.Open Subgroup

namespace Lemma39

variable {G : Type*} [Group G]

theorem zpow_eq_one_or_self {a : G} (ha : a ^ 2 = 1) (k : ℤ) : a ^ k = 1 ∨ a ^ k = a := by
  have hsq : a * a = 1 := by rw [← pow_two]; exact ha
  have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
  have hpow : a ^ k = a ^ (k % 2) := by
    conv_lhs => rw [hk]
    rw [zpow_add, zpow_mul, zpow_two, hsq, one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hpow, h, zpow_zero]
  · right
    rw [hpow, h, zpow_one]

theorem mem_zpowers_sup {Y : Subgroup G} {a : G} (ha : a ^ 2 = 1)
    (haY : a ∈ normalizer (Y : Set G)) {x : G} (hx : x ∈ zpowers a ⊔ Y) :
    x ∈ Y ∨ ∃ y ∈ Y, x = a * y := by
  have hle : zpowers a ≤ normalizer (Y : Set G) := zpowers_le.2 haY
  have hxs : x ∈ ((zpowers a ⊔ Y : Subgroup G) : Set G) := hx
  rw [coe_mul_of_left_le_normalizer_right _ _ hle] at hxs
  obtain ⟨c, hc, y, hy, rfl⟩ := Set.mem_mul.1 hxs
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
  rcases zpow_eq_one_or_self ha k with h | h
  · left
    rw [h, one_mul]
    exact hy
  · right
    exact ⟨y, hy, by rw [h]⟩

theorem mem_of_mem_zpowers_sup_of_mem {L Y : Subgroup G} {a : G} (ha : a ^ 2 = 1)
    (haY : a ∈ normalizer (Y : Set G)) (hYL : Y ≤ L) (haL : a ∉ L) {x : G}
    (hx : x ∈ zpowers a ⊔ Y) (hxL : x ∈ L) : x ∈ Y := by
  rcases mem_zpowers_sup ha haY hx with h | ⟨y, hy, rfl⟩
  · exact h
  · exfalso
    apply haL
    have : a = (a * y) * y⁻¹ := by group
    rw [this]
    exact L.mul_mem hxL (L.inv_mem (hYL hy))

theorem mem_normalizer_sup {H K : Subgroup G} {g : G} (hH : g ∈ normalizer (H : Set G))
    (hK : g ∈ normalizer (K : Set G)) : g ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

theorem mem_normalizer_inf_centralizer {L : Subgroup G} {a g : G}
    (hgL : g ∈ normalizer (L : Set G)) (hga : g * a = a * g) :
    g ∈ normalizer ((L ⊓ centralizer ({a} : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  simp only [mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hxL, hxa⟩
    refine ⟨(mem_normalizer_iff.1 hgL x).1 hxL, ?_⟩
    calc g * x * g⁻¹ * a = g * x * (g⁻¹ * a * g) * g⁻¹ := by group
      _ = g * x * a * g⁻¹ := by
          rw [show g⁻¹ * a * g = a by
            calc g⁻¹ * a * g = g⁻¹ * (g * a) := by rw [hga]; group
              _ = a := by group]
      _ = g * (a * x) * g⁻¹ := by rw [mul_assoc g x a, ← hxa]
      _ = a * (g * x * g⁻¹) := by
          calc g * (a * x) * g⁻¹ = (g * a) * x * g⁻¹ := by group
            _ = (a * g) * x * g⁻¹ := by rw [hga]
            _ = a * (g * x * g⁻¹) := by group
  · rintro ⟨hxL, hxa⟩
    refine ⟨(mem_normalizer_iff.1 hgL x).2 hxL, ?_⟩
    have hga' : g⁻¹ * a = a * g⁻¹ := by
      calc g⁻¹ * a = g⁻¹ * (a * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * a) * g⁻¹ := by rw [hga]
        _ = a * g⁻¹ := by group
    calc x * a = g⁻¹ * (g * x * g⁻¹) * (g * a) := by group
      _ = g⁻¹ * (g * x * g⁻¹) * (a * g) := by rw [hga]
      _ = g⁻¹ * ((g * x * g⁻¹) * a) * g := by group
      _ = g⁻¹ * (a * (g * x * g⁻¹)) * g := by rw [hxa]
      _ = (g⁻¹ * a) * (g * x * g⁻¹) * g := by group
      _ = (a * g⁻¹) * (g * x * g⁻¹) * g := by rw [hga']
      _ = a * x := by group

theorem center_eq_bot {L : Type*} [Group L] [IsSimpleGroup L] (hLd : HasDihedralSylowTwo L) :
    center L = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center L) with h | h
  · exact h
  · exfalso
    obtain ⟨S, n, hn, ⟨e⟩⟩ := hLd
    have hcomm : ∀ x y : L, x * y = y * x := fun x y =>
      (mem_center_iff.1 (h ▸ mem_top x : x ∈ center L) y).symm
    let _ : CommGroup L := { (inferInstance : Group L) with mul_comm := hcomm }
    have : IsCyclic L := IsSimpleGroup.isCyclic
    have hS : IsCyclic (S : Subgroup L) := inferInstance
    have hD : IsCyclic (DihedralGroup (2 ^ (n - 1))) := e.isCyclic.1 hS
    exact DihedralGroup.not_isCyclic (by
      have : 1 ≤ n - 1 := by omega
      have h2 : 2 ≤ 2 ^ (n - 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) this
      omega) hD

theorem eq_one_of_mem_of_mem_centralizer {L : Subgroup G} [IsSimpleGroup L]
    (hLd : HasDihedralSylowTwo L) {x : G} (hxL : x ∈ L)
    (hxC : x ∈ centralizer (L : Set G)) : x = 1 := by
  have hc : (⟨x, hxL⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro l
    exact Subtype.ext ((mem_centralizer_iff.1 hxC) l l.2)
  rw [center_eq_bot hLd, mem_bot] at hc
  exact congrArg Subtype.val hc

theorem centralizer_le_of_maximal {L : Subgroup G} {a b : G} (ha : a ^ 2 = 1)
    (haN : a ∈ normalizer (L : Set G)) (hab : a * b = b * a) (haL : a ∉ L)
    (hmax : ∀ K : Subgroup G, zpowers a ⊔ (L ⊓ centralizer ({a} : Set G)) ≤ K →
      K ≤ zpowers a ⊔ L →
      K = zpowers a ⊔ (L ⊓ centralizer ({a} : Set G)) ∨ K = zpowers a ⊔ L)
    (hgen : ¬ L ≤ (L ⊓ centralizer ({a} : Set G)) ⊔ (L ⊓ centralizer ({b} : Set G))) :
    L ⊓ centralizer ({b} : Set G) ≤ L ⊓ centralizer ({a} : Set G) := by
  set Ca := L ⊓ centralizer ({a} : Set G)
  set Cb := L ⊓ centralizer ({b} : Set G)
  have haCa : a ∈ normalizer (Ca : Set G) := mem_normalizer_inf_centralizer haN rfl
  have haCb : a ∈ normalizer (Cb : Set G) := mem_normalizer_inf_centralizer haN hab
  have haY : a ∈ normalizer ((Ca ⊔ Cb : Subgroup G) : Set G) := mem_normalizer_sup haCa haCb
  have hYL : Ca ⊔ Cb ≤ L := sup_le inf_le_left inf_le_left
  rcases hmax (zpowers a ⊔ (Ca ⊔ Cb)) (sup_le_sup_left le_sup_left _)
      (sup_le_sup_left hYL _) with h | h
  · intro x hx
    have hxM : x ∈ zpowers a ⊔ Ca := h ▸ (mem_sup_right (mem_sup_right hx))
    exact mem_of_mem_zpowers_sup_of_mem ha haCa inf_le_left haL hxM (mem_inf.1 hx).1
  · exfalso
    apply hgen
    intro l hl
    have hlK : l ∈ zpowers a ⊔ (Ca ⊔ Cb) := h ▸ mem_sup_right hl
    exact mem_of_mem_zpowers_sup_of_mem ha haY hYL haL hlK hl

end Lemma39

open Lemma39

theorem lemma_3_9 (hK : AschbacherKnownGroupFacts) {G : Type} [Group G] [Finite G]
    (L : Subgroup G) [IsSimpleGroup L] (hLd : HasDihedralSylowTwo L) {a b : G}
    (haN : a ∈ normalizer (L : Set G)) (hbN : b ∈ normalizer (L : Set G))
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b = b * a)
    (hca : HasCyclicSylowTwo (L ⊓ centralizer ({a} : Set G) : Subgroup G))
    (hcb : HasCyclicSylowTwo (L ⊓ centralizer ({b} : Set G) : Subgroup G))
    (hgen : ¬ L ≤ (L ⊓ centralizer ({a} : Set G)) ⊔ (L ⊓ centralizer ({b} : Set G))) :
    a * b ∈ centralizer (L : Set G) := by
  obtain ⟨hout, hmax, hcenter, hcoset⟩ :=
    hK.dihedral_outer_involution G L a inferInstance hLd haN ha hca
  obtain ⟨houtb, hmaxb, -, -⟩ :=
    hK.dihedral_outer_involution G L b inferInstance hLd hbN hb hcb
  set Ca := L ⊓ centralizer ({a} : Set G) with hCa
  set Cb := L ⊓ centralizer ({b} : Set G) with hCb
  set M := zpowers a ⊔ Ca with hM
  have haL : a ∉ L := fun h => hout (mem_sup_left h)
  have hbL : b ∉ L := fun h => houtb (mem_sup_left h)
  have hasq : a * a = 1 := by rw [← pow_two]; exact ha
  have hba : Cb ≤ Ca := centralizer_le_of_maximal ha haN hab haL hmax hgen
  have hab' : Ca ≤ Cb := centralizer_le_of_maximal hb hbN hab.symm hbL hmaxb
    (by rwa [sup_comm])
  have hlc : a * b ∈ ((L ⊔ centralizer (L : Set G) : Subgroup G) : Set G) :=
    hcoset b hbN hb hcb
  rw [coe_mul_of_right_le_normalizer_left _ _ (centralizer_le_normalizer (L : Set G))] at hlc
  obtain ⟨l, hl, c, hc, hlc⟩ := Set.mem_mul.1 hlc
  set y := a * l with hy
  have hbyc : b = y * c := by
    calc b = a⁻¹ * (a * b) := by group
      _ = a * (l * c) := by rw [← hlc, inv_eq_of_mul_eq_one_left hasq]
      _ = y * c := by rw [hy, mul_assoc]
  have hcL : ∀ x ∈ L, c * x = x * c := fun x hx => ((mem_centralizer_iff.1 hc) x hx).symm
  have hyact : ∀ x ∈ L, y * x * y⁻¹ = b * x * b⁻¹ := by
    intro x hx
    rw [hbyc]
    calc y * x * y⁻¹ = y * (x * c) * c⁻¹ * y⁻¹ := by group
      _ = y * (c * x) * c⁻¹ * y⁻¹ := by rw [hcL x hx]
      _ = y * c * x * (y * c)⁻¹ := by group
  have hALN : zpowers a ⊔ L ≤ normalizer (L : Set G) :=
    sup_le (zpowers_le.2 haN) le_normalizer
  have hyAL : y ∈ zpowers a ⊔ L := mul_mem (mem_sup_left (mem_zpowers a)) (mem_sup_right hl)
  have hcentral : ∀ w ∈ zpowers a ⊔ L, w ∈ centralizer (L : Set G) → w = 1 := by
    intro w hw hwC
    rcases mem_zpowers_sup ha haN hw with hwL | ⟨l', hl', rfl⟩
    · exact eq_one_of_mem_of_mem_centralizer hLd hwL hwC
    · exfalso
      apply hout
      have : a = (a * l') * l'⁻¹ := by group
      rw [this]
      exact mul_mem (mem_sup_right hwC) (mem_sup_left (L.inv_mem hl'))
  have hanC : ∀ z ∈ centralizer (L : Set G), a * z * a⁻¹ ∈ centralizer (L : Set G) := by
    intro z hz
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : a⁻¹ * x * a ∈ L := by
      have := (mem_normalizer_iff.1 (inv_mem haN) x).1 hx
      simpa using this
    have hzx := (mem_centralizer_iff.1 hz) (a⁻¹ * x * a) hx'
    calc x * (a * z * a⁻¹) = a * ((a⁻¹ * x * a) * z) * a⁻¹ := by group
      _ = a * (z * (a⁻¹ * x * a)) * a⁻¹ := by rw [hzx]
      _ = a * z * a⁻¹ * x := by group
  have hya : y * a = a * y := by
    have hrel : y⁻¹ * a * y = c * a * c⁻¹ := by
      calc y⁻¹ * a * y = y⁻¹ * (a * (y * c)) * c⁻¹ := by group
        _ = y⁻¹ * ((y * c) * a) * c⁻¹ := by rw [← hbyc, hab, hbyc]
        _ = c * a * c⁻¹ := by group
    have hwC : c * a * c⁻¹ * a⁻¹ ∈ centralizer (L : Set G) := by
      have : c * a * c⁻¹ * a⁻¹ = c * (a * c⁻¹ * a⁻¹) := by group
      rw [this]
      exact mul_mem hc (hanC _ (inv_mem hc))
    have hwAL : c * a * c⁻¹ * a⁻¹ ∈ zpowers a ⊔ L := by
      rw [← hrel]
      exact mul_mem (mul_mem (mul_mem (inv_mem hyAL) (mem_sup_left (mem_zpowers a))) hyAL)
        (inv_mem (mem_sup_left (mem_zpowers a)))
    have h1 := hcentral _ hwAL hwC
    rw [← hrel] at h1
    calc y * a = y * (y⁻¹ * a * y * a⁻¹) * a := by rw [h1]; group
      _ = a * y := by group
  have hyN : y ∈ normalizer (M : Set G) := by
    refine mem_normalizer_sup ?_ (mem_normalizer_inf_centralizer (hALN hyAL) hya)
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (y * a * y⁻¹) = zpowers a
    rw [hya, mul_inv_cancel_right]
  have haCa : a ∈ normalizer (Ca : Set G) := mem_normalizer_inf_centralizer haN rfl
  have hyM : y ∈ M := by
    have hMAL : M ≤ zpowers a ⊔ L := sup_le le_sup_left (inf_le_left.trans le_sup_right)
    rcases hmax (M ⊔ zpowers y) le_sup_left (sup_le hMAL (zpowers_le.2 hyAL)) with h | h
    · exact h ▸ mem_sup_right (mem_zpowers y)
    · exfalso
      have hLN : L ≤ normalizer (M : Set G) := by
        calc L ≤ zpowers a ⊔ L := le_sup_right
          _ = M ⊔ zpowers y := h.symm
          _ ≤ normalizer (M : Set G) := sup_le le_normalizer (zpowers_le.2 hyN)
      have hconj : ∀ l' ∈ L, ∀ x ∈ Ca, l' * x * l'⁻¹ ∈ Ca := by
        intro l' hl' x hx
        have hxM : l' * x * l'⁻¹ ∈ M :=
          (mem_normalizer_iff.1 (hLN hl') x).1 (mem_sup_right hx)
        exact mem_of_mem_zpowers_sup_of_mem ha haCa inf_le_left haL hxM
          (L.mul_mem (L.mul_mem hl' (mem_inf.1 hx).1) (L.inv_mem hl'))
      have hnormal : (Ca.subgroupOf L).Normal := by
        refine ⟨fun x hx g => ?_⟩
        rw [mem_subgroupOf] at hx ⊢
        simpa using hconj g g.2 x hx
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Ca.subgroupOf L) with h0 | h0
      ·
        obtain ⟨l₀, hl₀⟩ := exists_ne (1 : L)
        apply hl₀
        have hla : (l₀ : G) * a * (l₀ : G)⁻¹ ∈ M :=
          (mem_normalizer_iff.1 (hLN l₀.2) a).1 (mem_sup_left (mem_zpowers a))
        rcases mem_zpowers_sup ha haCa hla with h1 | ⟨x, hx, h1⟩
        · exfalso
          apply haL
          have hx1 : (⟨_, (mem_inf.1 h1).1⟩ : L) ∈ Ca.subgroupOf L := h1
          rw [h0, mem_bot] at hx1
          have h2 : (l₀ : G) * a * (l₀ : G)⁻¹ = 1 := congrArg Subtype.val hx1
          have : a = 1 := by
            calc a = (l₀ : G)⁻¹ * ((l₀ : G) * a * (l₀ : G)⁻¹) * l₀ := by group
              _ = 1 := by rw [h2]; group
          rw [this]
          exact L.one_mem
        · have hx1 : (⟨x, (mem_inf.1 hx).1⟩ : L) ∈ Ca.subgroupOf L := hx
          rw [h0, mem_bot] at hx1
          have hx0 : x = 1 := congrArg Subtype.val hx1
          rw [hx0, mul_one] at h1
          have hl₀C : l₀ ∈ Ca.subgroupOf L := by
            rw [mem_subgroupOf]
            refine mem_inf.2 ⟨l₀.2, mem_centralizer_singleton_iff.2 ?_⟩
            calc (l₀ : G) * a = (l₀ : G) * a * (l₀ : G)⁻¹ * l₀ := by group
              _ = a * l₀ := by rw [h1]
          rw [h0, mem_bot] at hl₀C
          exact hl₀C
      ·
        apply hout
        apply mem_sup_right
        rw [mem_centralizer_iff]
        intro x hx
        have hx1 : (⟨x, hx⟩ : L) ∈ Ca.subgroupOf L := h0 ▸ mem_top _
        exact mem_centralizer_singleton_iff.1 (mem_inf.1 hx1).2
  have hyZ : y ∈ zpowers a := by
    refine hcenter y hyM (fun m hm => ?_)
    have hMC : M ≤ centralizer ({y} : Set G) := by
      refine sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hya.symm)) ?_
      intro x hx
      rw [mem_centralizer_singleton_iff]
      have hxb : x * b = b * x := mem_centralizer_singleton_iff.1 (mem_inf.1 (hab' hx)).2
      have := hyact x (mem_inf.1 hx).1
      symm
      calc y * x = (y * x * y⁻¹) * y := by group
        _ = (b * x * b⁻¹) * y := by rw [this]
        _ = x * y := by rw [← hxb]; group
    exact (mem_centralizer_singleton_iff.1 (hMC hm)).symm
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hyZ
  rcases zpow_eq_one_or_self ha k with h1 | h1
  ·
    exfalso
    apply houtb
    rw [hbyc, ← hk, h1, one_mul]
    exact mem_sup_right hc
  · rw [hbyc, ← hk, h1, ← mul_assoc, hasq, one_mul]
    exact hc

end CFSG.ComponentClassification.AschbacherKnownGroup
