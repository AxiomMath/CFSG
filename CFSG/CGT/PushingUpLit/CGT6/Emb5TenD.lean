module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5Nine
public import CFSG.CGT.PushingUpLit.CGT6.EmbThree
public import CFSG.CGT.PushingUpLit.CGT6.Emb5EightC

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUp
open scoped commutatorElement

section Aux

variable {Γ : Type*} [Group Γ]

theorem perfect_le_of_le_sup {L Y P K : Subgroup Γ}
    (hLK : ∀ k ∈ K, ∀ l ∈ L, k * l * k⁻¹ ∈ L) (hYK : Y ≤ K)
    (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hP : Group.IsPerfect ↥P) (hPLY : P ≤ L ⊔ Y) :
    P ≤ L := by
  have hmem : ∀ g ∈ L ⊔ Y, ∃ l ∈ L, ∃ y ∈ Y, g = l * y := by
    let S : Subgroup Γ :=
      { carrier := {g | ∃ l ∈ L, ∃ y ∈ Y, g = l * y}
        one_mem' := ⟨1, L.one_mem, 1, Y.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨l₁, hl₁, y₁, hy₁, rfl⟩ ⟨l₂, hl₂, y₂, hy₂, rfl⟩
          refine ⟨l₁ * (y₁ * l₂ * y₁⁻¹), L.mul_mem hl₁ (hLK y₁ (hYK hy₁) l₂ hl₂), y₁ * y₂,
            Y.mul_mem hy₁ hy₂, ?_⟩
          group
        inv_mem' := by
          rintro _ ⟨l, hl, y, hy, rfl⟩
          refine ⟨y⁻¹ * l⁻¹ * y⁻¹⁻¹, hLK y⁻¹ (K.inv_mem (hYK hy)) l⁻¹ (L.inv_mem hl), y⁻¹,
            Y.inv_mem hy, ?_⟩
          group }
    have : L ⊔ Y ≤ S := sup_le (fun l hl => ⟨l, hl, 1, Y.one_mem, by simp⟩)
      (fun y hy => ⟨1, L.one_mem, y, hy, by simp⟩)
    exact fun g hg => this hg
  calc P = ⁅P, P⁆ := (Subgroup.isPerfect_iff.mp hP).symm
    _ ≤ L := by
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      obtain ⟨l₁, hl₁, y₁, hy₁, rfl⟩ := hmem a (hPLY ha)
      obtain ⟨l₂, hl₂, y₂, hy₂, rfl⟩ := hmem b (hPLY hb)
      have hy12 : y₁ * y₂ = y₂ * y₁ := hYc y₁ hy₁ y₂ hy₂
      have h1 : l₁ * (y₁ * l₂ * y₁⁻¹) ∈ L :=
        L.mul_mem hl₁ (hLK y₁ (hYK hy₁) l₂ hl₂)
      have h2 : l₂ * (y₂ * l₁ * y₂⁻¹) ∈ L :=
        L.mul_mem hl₂ (hLK y₂ (hYK hy₂) l₁ hl₁)
      have e : ⁅l₁ * y₁, l₂ * y₂⁆ =
          (l₁ * (y₁ * l₂ * y₁⁻¹)) * (l₂ * (y₂ * l₁ * y₂⁻¹))⁻¹ := by
        simp only [commutatorElement_def]
        calc l₁ * y₁ * (l₂ * y₂) * (l₁ * y₁)⁻¹ * (l₂ * y₂)⁻¹
            = ((l₁ * (y₁ * l₂ * y₁⁻¹)) * (y₁ * y₂)) *
                ((l₂ * (y₂ * l₁ * y₂⁻¹)) * (y₂ * y₁))⁻¹ := by group
          _ = ((l₁ * (y₁ * l₂ * y₁⁻¹)) * (y₁ * y₂)) *
                ((l₂ * (y₂ * l₁ * y₂⁻¹)) * (y₁ * y₂))⁻¹ := by rw [hy12]
          _ = _ := by group
      rw [e]
      exact L.mul_mem h1 (L.inv_mem h2)

theorem closure_comm_of_pairwise {Δ : Type*} [Group Δ] {S : Set Δ}
    (h : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) :
    ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S := by
    rw [Subgroup.closure_le]
    intro a ha b hb
    exact (h b hb a ha)
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure S : Set Δ) := by
    rw [Subgroup.closure_le]
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (h1 hb) a ha).symm
  intro a ha b hb
  exact (Subgroup.mem_centralizer_iff.mp (h2 ha) b hb).symm

end Aux

section D0

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

omit [Finite V] in
theorem comm_of_card_three {Γ : Type*} [Group Γ] {Y : Subgroup Γ} (h3 : Nat.card ↥Y = 3) :
    ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : IsCyclic ↥Y := isCyclic_of_prime_card h3
  intro a ha b hb
  have := hc.isMulCommutative.is_comm.comm (⟨a, ha⟩ : ↥Y) ⟨b, hb⟩
  exact congrArg Subtype.val this

omit [Finite V] in
theorem normalizer_of_forall_conj {L G' : Subgroup (MulAut V)}
    (hn : ∀ g ∈ G', ∀ x ∈ L, g * x * g⁻¹ ∈ L) {g : MulAut V} (hg : g ∈ G') :
    g ∈ Subgroup.normalizer (L : Set (MulAut V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hn g hg x, fun hx => ?_⟩
  have := hn g⁻¹ (G'.inv_mem hg) _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at this

omit [Finite V] in
theorem conjSub_eq_of_centralizes {t : MulAut V} {Y : Subgroup (MulAut V)}
    (hy : ∀ y ∈ Y, t * y = y * t) : CGT6E.conjSub t Y = Y := by
  ext z
  rw [CGT6E.mem_conjSub]
  constructor
  · rintro ⟨y, hy', rfl⟩
    have : t * y * t⁻¹ = y := by rw [hy y hy']; group
    rw [this]; exact hy'
  · intro hz
    refine ⟨z, hz, ?_⟩
    rw [hy z hz]; group

omit [Finite V] in
theorem mem_normalizer_sup_of_conjSub {A B : Subgroup (MulAut V)} {t : MulAut V}
    (hA : CGT6E.conjSub t A = A) (hB : CGT6E.conjSub t B = B) :
    t ∈ Subgroup.normalizer ((A ⊔ B : Subgroup (MulAut V)) : Set (MulAut V)) := by
  apply mem_normalizer_of_conjSub_eq
  unfold CGT6E.conjSub at *
  rw [Subgroup.map_sup, hA, hB]

theorem Emb5Cfg.LYT_le_normalizer (cfg : Emb5Cfg G T Y) {L : Subgroup (MulAut V)}
    (h : Emb5Layer G Y L) :
    L ⊔ Y ⊔ T ≤ Subgroup.normalizer ((L ⊔ Y : Subgroup (MulAut V)) : Set (MulAut V)) := by
  refine sup_le Subgroup.le_normalizer ?_
  intro t ht
  have hLn := conjSub_eq_of_mem_normalizer (normalizer_of_forall_conj h.normal (cfg.adm.hTG ht))
  have hYn := conjSub_eq_of_centralizes (Y := Y) (t := t) fun y hy =>
    (Subgroup.mem_centralizer_iff.mp (cfg.adm.le_centralizer ht) y hy).symm
  exact mem_normalizer_sup_of_conjSub hLn hYn

theorem Emb5Cfg.sup_eq_LYT (cfg : Emb5Cfg G T Y) (hV : ∀ v : V, v ^ 2 = 1)
    {L : Subgroup (MulAut V)} (h : Emb5Layer G Y L) : L ⊔ Y ⊔ T = G := by
  have hYG : Y ≤ G := fun y hy => (cfg.adm.hYC hy).1
  set K : Subgroup (MulAut V) := L ⊔ Y ⊔ T with hK
  have hKG : K ≤ G := sup_le (sup_le h.le hYG) cfg.adm.hTG
  have hLY : L ⊔ Y ≤ K := le_sup_left
  have hLK : L ≤ K := le_sup_left.trans hLY
  have hYK : Y ≤ K := le_sup_right.trans hLY
  have hTK : T ≤ K := le_sup_right
  have hKN : K ≤ Subgroup.normalizer ((L ⊔ Y : Subgroup (MulAut V)) : Set (MulAut V)) :=
    cfg.LYT_le_normalizer h
  by_contra hne
  have hlt : K < G := lt_of_le_of_ne hKG hne
  have hadm : Adm5 K T Y := cfg.adm.restrict hTK hKG hYK
  obtain ⟨X₁, hX₁⟩ := cfg.lift_sub hV hlt hadm
  have h3 := cfg.adm.h3
  by_cases hperf : ⁅X₁, X₁⁆ = X₁
  ·
    have hcc : conjClosure Y X₁ = X₁ := Lift5.conjClosure_eq cfg.not_isPGroup_Y hX₁
    obtain ⟨hYX, hXK, hsubX, hc, harr⟩ := hX₁
    have hX₁LY : X₁ ≤ L ⊔ Y := by
      rw [← hcc, conjClosure, Subgroup.closure_le]
      rintro _ ⟨g, hg, y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hKN (hXK hg)) y).mp (Subgroup.mem_sup_right hy)
    have hXL : X₁ ≤ L :=
      perfect_le_of_le_sup (K := K) (fun k hk l hl => h.normal k (hKG hk) l hl) hYK
        (comm_of_card_three h3) (Subgroup.isPerfect_iff.mpr hperf) hX₁LY
    have hsubL : (X₁.subgroupOf L).IsSubnormal :=
      CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hLK hsubX
    have hLG : (L.subgroupOf G).IsSubnormal := by
      have : (L.subgroupOf G).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mpr fun g hg =>
          normalizer_of_forall_conj h.normal hg
      exact this.isSubnormal
    have hsubG := CFSG.GroupTheory.isSubnormal_subgroupOf_trans hXL h.le hsubL hLG
    exact cfg.nolift ⟨X₁, hYX, hXK.trans hKG, hsubG, hc, harr⟩
  ·
    have hHN : K ≤ Subgroup.normalizer (oTwoIn K : Set (MulAut V)) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoIn K)
    have hO : ⁅oTwoIn Y, Y⁆ = ⊥ := by
      rw [oTwoIn_eq_bot_of_card_three h3]
      exact Subgroup.commutator_bot_left Y
    have hQY : ⁅oTwoIn K, Y⁆ = ⊥ :=
      commutator_eq_bot_of_centralizer (G₀ := K) (T := T) (Y := Y) (Q := oTwoIn K)
        (noTwoQuotient_of_card_three h3) (Or.inr h3) hO hadm.hT2 (SixThree.isPGroup_oTwoIn K)
        (oTwoIn_le K) (hTK.trans hHN) (hYK.trans hHN) hadm.hYC hadm.hsub
    have hsubY := Lift5.subnormal_of_not_perfect hV h3 hX₁ hperf hQY
    have hp3Y : IsPGroup 3 ↥(Y.subgroupOf K) :=
      (IsPGroup.of_card (n := 1) (by simpa using h3) : IsPGroup 3 ↥Y).of_equiv
        (Subgroup.subgroupOfEquivOfLe hYK).symm
    have hle : Y.subgroupOf K ≤ pCore 3 ↥K := le_pCore_of_isSubnormal hsubY hp3Y
    have : (L.subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLK).mpr fun k hk =>
        normalizer_of_forall_conj h.normal (hKG hk)
    have hqs : CFSG.IsQuasisimple ↥(L.subgroupOf K) :=
      isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLK).symm h.quasi
    obtain ⟨y, hy, x, hx, hxy⟩ := h.noncentral
    have hyK : (⟨y, hYK hy⟩ : ↥K) ∈ pCore 3 ↥K := hle (Subgroup.mem_subgroupOf.mpr hy)
    have : (pCore 3 ↥K).Normal := pCore_normal
    rcases le_or_commute_of_normal hqs hyK with hLP | hcomm
    · have hp : IsPGroup 3 ↥(L.subgroupOf K) := (pCore_isPGroup (p := 3) (G := ↥K)).to_le hLP
      have hs := subsingleton_of_perfect_of_isPGroup hqs.1 hp
      have := nontrivial_of_isQuasisimple hqs
      exact not_subsingleton _ hs |>.elim
    · exact hxy (congrArg Subtype.val (hcomm ⟨x, hLK hx⟩ (Subgroup.mem_subgroupOf.mpr hx)))

omit [Finite V] in
theorem conjSub_le_of_mem {g : MulAut V} (hg : g ∈ G) (hYG : Y ≤ G) :
    CGT6E.conjSub g Y ≤ G := by
  rintro _ ⟨y, hy, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact G.mul_mem (G.mul_mem hg (hYG hy)) (G.inv_mem hg)

theorem Emb5Cfg.exists_layer' (cfg : Emb5Cfg G T Y) (hV : ∀ v : V, v ^ 2 = 1) :
    ∃ L, Emb5Layer G Y L :=
  cfg.exists_layer hV fun hsub =>
    Lift5.of_subnormal hV cfg.adm.h3 cfg.adm.h4 (fun _ hy => (cfg.adm.hYC hy).1) hsub

theorem Emb5Cfg.le_layer_of_forall (cfg : Emb5Cfg G T Y) (hV : ∀ v : V, v ^ 2 = 1) {t : MulAut V}
    (ht : t ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V))) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hforall : ∀ g ∈ G, CGT6E.conjSub g Y ⊔ Y ⊔ Subgroup.zpowers t ≠ G)
    {L : Subgroup (MulAut V)} (h : Emb5Layer G Y L) : Y ≤ L := by
  by_contra hYL
  have hYG : Y ≤ G := fun y hy => (cfg.adm.hYC hy).1
  have hGeq : L ⊔ Y ⊔ T = G := cfg.sup_eq_LYT hV h
  have hGN : G ≤ Subgroup.normalizer ((L ⊔ Y : Subgroup (MulAut V)) : Set (MulAut V)) := by
    rw [← hGeq]; exact cfg.LYT_le_normalizer h
  have hNLY : conjClosure Y G ≤ L ⊔ Y := by
    rw [conjClosure, Subgroup.closure_le]
    rintro _ ⟨g, hg, y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hGN hg) y).mp (Subgroup.mem_sup_right hy)
  have h3 := cfg.adm.h3
  have htG : t ∈ G := ht.1
  have hcomm : ∀ g ∈ G, ∀ a ∈ CGT6E.conjSub g Y, ∀ b ∈ Y, a * b = b * a := by
    intro g hg
    obtain ⟨-, hc | ⟨B, hB, hlift⟩⟩ := cfg.five_nine hV ht ht1 ht2 hg (hforall g hg)
    · exact hc
    · exfalso
      have hHG : CGT6E.conjSub g Y ⊔ Y ⊔ Subgroup.zpowers t ≤ G :=
        sup_le (sup_le (conjSub_le_of_mem hg hYG) hYG) (Subgroup.zpowers_le.mpr htG)
      have hcc : conjClosure Y B = B := Lift5.conjClosure_eq cfg.not_isPGroup_Y hlift
      have hBN : B ≤ L ⊔ Y := by
        rw [← hcc]
        exact (conjClosure_mono (hlift.2.1.trans hHG)).trans hNLY
      have hBL : B ≤ L :=
        perfect_le_of_le_sup (K := G) (fun k hk l hl => h.normal k hk l hl) hYG
          (comm_of_card_three h3) (Subgroup.isPerfect_iff.mpr hB) hBN
      exact hYL (hlift.1.trans hBL)
  have hpair : ∀ a ∈ {x | ∃ g ∈ G, ∃ y ∈ Y, x = g * y * g⁻¹},
      ∀ b ∈ {x | ∃ g ∈ G, ∃ y ∈ Y, x = g * y * g⁻¹}, a * b = b * a := by
    rintro _ ⟨g₁, hg₁, y₁, hy₁, rfl⟩ _ ⟨g₂, hg₂, y₂, hy₂, rfl⟩
    have hg : g₁⁻¹ * g₂ ∈ G := G.mul_mem (G.inv_mem hg₁) hg₂
    have h1 := hcomm _ hg (g₁⁻¹ * g₂ * y₂ * (g₁⁻¹ * g₂)⁻¹) (CGT6E.conj_mem_conjSub hy₂) y₁ hy₁
    calc g₁ * y₁ * g₁⁻¹ * (g₂ * y₂ * g₂⁻¹)
        = g₁ * (y₁ * (g₁⁻¹ * g₂ * y₂ * (g₁⁻¹ * g₂)⁻¹)) * g₁⁻¹ := by group
      _ = g₁ * ((g₁⁻¹ * g₂ * y₂ * (g₁⁻¹ * g₂)⁻¹) * y₁) * g₁⁻¹ := by rw [← h1]
      _ = g₂ * y₂ * g₂⁻¹ * (g₁ * y₁ * g₁⁻¹) := by group
  have hNcomm := closure_comm_of_pairwise hpair
  obtain ⟨a, b, hab⟩ := exists_not_comm_of_isQuasisimple h.quasi
  exact hab (Subtype.ext (hNcomm a (h.le_conj a.2) b (h.le_conj b.2)))

end D0

end CFSG.CGT.PushingUpLit.CGT6
