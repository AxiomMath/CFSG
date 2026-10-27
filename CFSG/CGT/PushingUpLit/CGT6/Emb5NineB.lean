module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5Nine

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUp
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem Emb5Cfg.lift_le_triple (cfg : Emb5Cfg G T Y) {t g : MulAut V}
    (htY : ∀ y ∈ Y, t * y = y * t) (ht2 : t ^ 2 = 1) {B : Subgroup (MulAut V)}
    (hlift : Lift5 (CGT6E.conjSub g Y ⊔ Y ⊔ Subgroup.zpowers t) Y B) :
    B ≤ CGT6E.conjSub g Y ⊔ CGT6E.conjSub t (CGT6E.conjSub g Y) ⊔ Y := by
  have hcc : conjClosure Y B = B := Lift5.conjClosure_eq cfg.not_isPGroup_Y hlift
  obtain ⟨-, hBH, -, -, -⟩ := hlift
  rw [← hcc]
  refine le_trans (conjClosure_mono hBH) ?_
  rw [conjClosure, Subgroup.closure_le]
  rintro _ ⟨g', hg', y, hy, rfl⟩
  have hyM : y ∈ CGT6E.conjSub g Y ⊔ CGT6E.conjSub t (CGT6E.conjSub g Y) ⊔ Y :=
    Subgroup.mem_sup_right hy
  have hn' := le_normalizer_triple (X := CGT6E.conjSub g Y) htY ht2 hg'
  exact (Subgroup.mem_normalizer_iff.mp hn' y).mp hyM

theorem Emb5Cfg.card_commV_lift_le (cfg : Emb5Cfg G T Y) {t g : MulAut V}
    (htY : ∀ y ∈ Y, t * y = y * t) (ht2 : t ^ 2 = 1) {B : Subgroup (MulAut V)}
    (hlift : Lift5 (CGT6E.conjSub g Y ⊔ Y ⊔ Subgroup.zpowers t) Y B) :
    Nat.card ↥(commV B) ≤ 64 := by
  have hBM := cfg.lift_le_triple htY ht2 hlift
  have hY4 := cfg.adm.h4
  have hX4 : Nat.card ↥(commV (CGT6E.conjSub g Y)) = 4 := by
    rw [CGT6E.card_commV_conjSub]; exact hY4
  have hXt4 : Nat.card ↥(commV (CGT6E.conjSub t (CGT6E.conjSub g Y))) = 4 :=
    (CGT6E.card_commV_conjSub t _).trans hX4
  exact (Subgroup.card_le_of_le (commV_mono hBM)).trans (card_commV_triple_le hX4 hXt4 hY4)

theorem Emb5Cfg.normalizes_of_lift' (cfg : Emb5Cfg G T Y) (hV : ∀ v : V, v ^ 2 = 1) {t g : MulAut V}
    (htY : ∀ y ∈ Y, t * y = y * t) (ht2 : t ^ 2 = 1) {B : Subgroup (MulAut V)}
    (hlift : Lift5 (CGT6E.conjSub g Y ⊔ Y ⊔ Subgroup.zpowers t) Y B) {n : ℕ} (hn : 2 ≤ n)
    (D : AltBlock B n) {x : MulAut V} (hx : x ∈ CGT6E.conjSub g Y ⊔ Y ⊔ Subgroup.zpowers t) :
    x ∈ Subgroup.normalizer (B : Set (MulAut V)) := by
  set X : Subgroup (MulAut V) := CGT6E.conjSub g Y with hX
  set Xt : Subgroup (MulAut V) := CGT6E.conjSub t X with hXt
  set H : Subgroup (MulAut V) := X ⊔ Y ⊔ Subgroup.zpowers t with hH
  set M₀ : Subgroup (MulAut V) := X ⊔ Xt ⊔ Y with hM₀
  have hlift' := hlift
  obtain ⟨hYB, hBH, hsubB, hc, -⟩ := hlift'
  have hxH : x ∈ H := hx
  by_contra hxN
  have hne : CGT6E.conjSub x B ≠ B := fun h => hxN (mem_normalizer_of_conjSub_eq h)
  obtain ⟨hA, hB'⟩ := trivial_of_conj_ne hV hBH hsubB hc hxH hne
  have hBM : B ≤ M₀ := cfg.lift_le_triple htY ht2 hlift
  have hxn : x ∈ Subgroup.normalizer (M₀ : Set (MulAut V)) :=
    le_normalizer_triple (X := X) htY ht2 hx
  have hB'M : CGT6E.conjSub x B ≤ M₀ := by
    rintro _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.mp hxn _).mp (hBM hb)
  have hle : commV B ⊔ commV (CGT6E.conjSub x B) ≤ commV M₀ :=
    sup_le (commV_mono hBM) (commV_mono hB'M)
  have hY4 := cfg.adm.h4
  have hX4 : Nat.card ↥(commV X) = 4 := by rw [hX, CGT6E.card_commV_conjSub]; exact hY4
  have hXt4 : Nat.card ↥(commV Xt) = 4 := by
    rw [hXt]; exact (CGT6E.card_commV_conjSub t X).trans hX4
  have hM64 : Nat.card ↥(commV M₀) ≤ 64 := card_commV_triple_le hX4 hXt4 hY4
  have hE : Nat.card ↥(commV B) = 2 ^ (2 * n) := D.card_commV
  have hE' : Nat.card ↥(commV (CGT6E.conjSub x B)) = Nat.card ↥(commV B) :=
    CGT6E.card_commV_conjSub x B
  have hdisj : commV B ⊓ commV (CGT6E.conjSub x B) = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨huE, huE'⟩
    rw [Subgroup.mem_bot]
    have hfix : ∀ b : ↥B, (b : MulAut V) u = u := fun b => hB' b b.2 u huE'
    have hmem : D.β ⟨u, huE⟩ ∈ fixV ((alternatingGroup (Fin (2 * n + 1))).map
        (coreAct (2 * n + 1))) := by
      rw [mem_fixV_map_iff]
      intro σ hσ i
      obtain ⟨b, rfl⟩ := D.θ_surj σ hσ
      have heq : coreAct (2 * n + 1) (D.θ b) (D.β ⟨u, huE⟩) = D.β ⟨u, huE⟩ := by
        rw [← D.equivar b ⟨u, huE⟩]
        congr 1
        exact Subtype.ext (hfix b)
      have := congrArg (fun w => vcoord w ((D.θ b) i)) heq
      simpa [vcoord_coreAct] using this.symm
    rw [fixV_alt_map (odd_two_mul_add_one n) (by omega)] at hmem
    have h1 : D.β ⟨u, huE⟩ = 1 := Subgroup.mem_bot.mp hmem
    have h2 : (⟨u, huE⟩ : ↥(commV B)) = 1 := D.β.injective (by rw [h1, map_one])
    exact congrArg Subtype.val h2
  have hcard := card_sup_mul_card_inf (commV B) (commV (CGT6E.conjSub x B))
  rw [hdisj, Subgroup.card_bot, mul_one, hE', hE] at hcard
  have h16 : 16 ≤ 2 ^ (2 * n) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcardle := Subgroup.card_le_of_le hle
  rw [hcard] at hcardle
  have := Nat.mul_le_mul h16 h16
  omega

theorem Emb5Cfg.adm_zpowers (cfg : Emb5Cfg G T Y) {t : MulAut V}
    (ht : t ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V))) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    {H : Subgroup (MulAut V)} (hHG : H ≤ G) (hYH : Y ≤ H) (htH : t ∈ H) :
    Adm5 H (Subgroup.zpowers t) Y := by
  have htY : ∀ y ∈ Y, t * y = y * t := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp ht.2 y hy).symm
  have hcent := cfg.cent t ht ht1 ht2
  exact
    { hTG := Subgroup.zpowers_le.mpr htH
      hT1 := zpowers_ne_bot ht1
      hT2 := isPGroup_zpowers_of_sq ht2
      hYC := by
        refine fun y hy => ⟨hYH hy, ?_⟩
        rw [centralizer_zpowers_eq]
        exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact htY y hy
      hsub := by
        rw [centralizer_zpowers_eq]
        exact CFSG.GroupTheory.isSubnormal_subgroupOf_of_le (inf_le_inf_right _ hHG) hcent
      h3 := cfg.adm.h3
      h4 := cfg.adm.h4 }

theorem Emb5Cfg.eq_of_conjClosure_le (cfg : Emb5Cfg G T Y) (hV : ∀ v : V, v ^ 2 = 1) {t : MulAut V}
    (ht : t ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V))) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    {K : Subgroup (MulAut V)} (hNK : conjClosure Y G ≤ K) (hKG : K ≤ G) (htK : t ∈ K) :
    K = G := by
  by_contra hne
  have hYG : Y ≤ G := fun y hy => (cfg.adm.hYC hy).1
  have hlt : K < G := lt_of_le_of_ne hKG hne
  have hYK : Y ≤ K := fun y hy =>
    hNK (Subgroup.subset_closure ⟨1, G.one_mem, y, hy, by simp⟩)
  obtain ⟨X, hX⟩ := cfg.lift_sub hV hlt (cfg.adm_zpowers ht ht1 ht2 hKG hYK htK)
  exact cfg.nolift ⟨X, Lift5.up hYG cfg.not_isPGroup_Y hNK hKG hX⟩

theorem Emb5Cfg.five_nine_struct (cfg : Emb5Cfg G T Y) (hV : ∀ v : V, v ^ 2 = 1) {t g : MulAut V}
    (ht : t ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V))) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hg : g ∈ G) (hH : CGT6E.conjSub g Y ⊔ Y ⊔ Subgroup.zpowers t ≠ G)
    (hnc : ¬ ∀ a ∈ CGT6E.conjSub g Y, ∀ b ∈ Y, a * b = b * a) :
    ∃ (B : Subgroup (MulAut V)) (m : ℕ) (D : AltBlock B m),
      Lift5 (CGT6E.conjSub g Y ⊔ Y ⊔ Subgroup.zpowers t) Y B ∧ ⁅B, B⁆ = B ∧
        CGT6E.conjSub g Y ≤ B ∧ 2 ≤ m ∧ m ≤ 3 ∧ (∀ b : ↥B, D.θ b = 1 → b = 1) ∧
        ∀ h ∈ CGT6E.conjSub g Y ⊔ Y ⊔ Subgroup.zpowers t,
          h ∈ Subgroup.normalizer (B : Set (MulAut V)) := by
  obtain ⟨-, hc | ⟨B, hperf, hlift⟩⟩ := cfg.five_nine hV ht ht1 ht2 hg hH
  · exact absurd hc hnc
  set X : Subgroup (MulAut V) := CGT6E.conjSub g Y with hX
  have h3 := cfg.adm.h3
  have hYG : Y ≤ G := fun y hy => (cfg.adm.hYC hy).1
  have hXG : X ≤ G := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact G.mul_mem (G.mul_mem hg (hYG hy)) (G.inv_mem hg)
  have hHG : X ⊔ Y ⊔ Subgroup.zpowers t ≤ G :=
    sup_le (sup_le hXG hYG) (Subgroup.zpowers_le.mpr ht.1)
  have htY : ∀ y ∈ Y, t * y = y * t := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp ht.2 y hy).symm
  obtain ⟨m, hm, D, hR⟩ := cfg.exists_altBlock_of_lift hV hHG hlift hperf
  have hnorm : ∀ h ∈ X ⊔ Y ⊔ Subgroup.zpowers t, h ∈ Subgroup.normalizer (B : Set (MulAut V)) :=
    fun h hh => cfg.normalizes_of_lift' hV htY ht2 hlift hm D hh
  have hm3 : m ≤ 3 := by
    have h64 := cfg.card_commV_lift_le htY ht2 hlift
    rw [D.card_commV] at h64
    have : 2 ^ (2 * m) ≤ 2 ^ 6 := by simpa using h64
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp this
    omega
  have hX3 : Nat.card ↥X = 3 := (CGT6E.card_conjSub g Y).trans h3
  have hX4 : Nat.card ↥(commV X) = 4 := by
    rw [hX, CGT6E.card_commV_conjSub]; exact cfg.adm.h4
  obtain ⟨y, hy, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
    by_contra hno
    push Not at hno
    have : Y = ⊥ := (Subgroup.eq_bot_iff_forall Y).mpr hno
    rw [this] at h3
    simp at h3
  set x : MulAut V := g * y * g⁻¹ with hxdef
  have hxX : x ∈ X := CGT6E.conj_mem_conjSub hy
  have hx1 : x ≠ 1 := by
    intro h
    apply hy1
    have : g * y * g⁻¹ = 1 := h
    simpa using this
  have hXz : Subgroup.zpowers x = X := CGT6E.zpowers_eq_of_card_three hX3 hxX hx1
  have hx3 : x ^ 3 = 1 := by
    have : (⟨x, hxX⟩ : ↥X) ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥X) (x := ⟨x, hxX⟩)
      rwa [hX3] at this
    simpa using congrArg Subtype.val this
  have hcx : Nat.card ↥(commV (Subgroup.zpowers x)) = 4 := by rw [hXz]; exact hX4
  have hxN := hnorm x (Subgroup.mem_sup_left (Subgroup.mem_sup_left hxX))
  have hYB : Y ≤ B := hlift.1
  have hXB : X ≤ B := by
    rcases D.normalizer_dichotomy hV hm hR hxN hx3 hcx with hcen | hxB
    · exfalso
      apply hnc
      intro a ha b hb
      rw [← hXz] at ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hbx : Commute b x := hcen b (hYB hb)
      exact ((hbx.symm).zpow_left k).eq
    · rw [← hXz]; exact Subgroup.zpowers_le.mpr hxB
  exact ⟨B, m, D, hlift, hperf, hXB, hm, hm3, hR, hnorm⟩

end CFSG.CGT.PushingUpLit.CGT6
