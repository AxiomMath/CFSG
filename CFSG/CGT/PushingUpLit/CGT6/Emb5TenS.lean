module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5EightC
public import CFSG.CGT.PushingUpLit.CGT6.Emb5Nine
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
open scoped commutatorElement

section Quot

variable {V : Type} [CommGroup V] (L : Subgroup (MulAut V))

abbrev LQ : Type := ↥L ⧸ Subgroup.center ↥L

@[expose] def lpi : ↥L →* LQ L := QuotientGroup.mk' (Subgroup.center ↥L)

variable {L}

@[expose] def tilde (A : Subgroup (MulAut V)) : Subgroup (LQ L) :=
  (A.subgroupOf L).map (lpi L)

theorem mem_tilde {A : Subgroup (MulAut V)} {s : LQ L} :
    s ∈ tilde A ↔ ∃ (a : MulAut V) (ha : a ∈ L), a ∈ A ∧ lpi L ⟨a, ha⟩ = s := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, x.2, hx, rfl⟩
  · rintro ⟨a, ha, haA, rfl⟩
    exact ⟨⟨a, ha⟩, haA, rfl⟩

theorem tilde_sup {A B : Subgroup (MulAut V)} (hA : A ≤ L) (hB : B ≤ L) :
    tilde (L := L) (A ⊔ B) = tilde (L := L) A ⊔ tilde (L := L) B := by
  unfold tilde
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem tilde_conj {A : Subgroup (MulAut V)} {l : MulAut V} (hl : l ∈ L) :
    (tilde (L := L) A).map (MulAut.conj (lpi L ⟨l, hl⟩)).toMonoidHom =
      tilde (L := L) (CGT6E.conjSub l A) := by
  ext s
  constructor
  · rintro ⟨_, hx, rfl⟩
    obtain ⟨a, ha, haA, rfl⟩ := mem_tilde.mp hx
    refine mem_tilde.mpr ⟨l * a * l⁻¹, L.mul_mem (L.mul_mem hl ha) (L.inv_mem hl),
      CGT6E.conj_mem_conjSub haA, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rfl
  · intro hs
    obtain ⟨b, hb, hbA, rfl⟩ := mem_tilde.mp hs
    obtain ⟨a, haA, rfl⟩ := CGT6E.mem_conjSub.mp hbA
    have ha : a ∈ L := by
      have h1 : l⁻¹ * (l * a * l⁻¹) * l ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl) hb) hl
      have e : l⁻¹ * (l * a * l⁻¹) * l = a := by group
      rwa [e] at h1
    refine ⟨lpi L ⟨a, ha⟩, mem_tilde.mpr ⟨a, ha, haA, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rfl

end Quot

section Central

theorem IsZ3E9A4A5.comm_or_alt {K : Type} [Group K] (h : IsZ3E9A4A5 K) :
    (∀ a b : K, a * b = b * a) ∨
      ∃ m : ℕ, (m = 4 ∨ m = 5) ∧ Nonempty (K ≃* alternatingGroup (Fin m)) := by
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · left
    intro a b
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  · left
    intro a b
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  · right
    exact ⟨4, Or.inl rfl, ⟨e⟩⟩
  · right
    exact ⟨5, Or.inr rfl, ⟨e⟩⟩

theorem eq_one_of_central_alt {K : Type} [Group K] {m : ℕ} (hm : 4 ≤ m)
    (e : K ≃* alternatingGroup (Fin m)) {z : K} (hz : ∀ a : K, a * z = z * a) : z = 1 := by
  have h1 : e z ∈ Subgroup.center (alternatingGroup (Fin m)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨a, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hz a]
  have hcard : 4 ≤ Nat.card (Fin m) := by simpa using hm
  rw [alternatingGroup.center_eq_bot hcard] at h1
  exact e.injective (by simpa using Subgroup.mem_bot.mp h1)

theorem isZ3E9A4A5_map_central {Λ : Type} [Group Λ] {Q : Type} [Group Q] (π : Λ →* Q)
    (hker : ∀ x, π x = 1 → x ∈ Subgroup.center Λ) {A B : Subgroup Λ}
    (hA : Nat.card ↥(A.map π) = 3) (hB : Nat.card ↥(B.map π) = 3) (h : IsZ3E9A4A5 ↥(A ⊔ B)) :
    IsZ3E9A4A5 ↥((A ⊔ B).map π) := by
  rcases h.comm_or_alt with hcomm | ⟨m, hm, ⟨e⟩⟩
  · rw [Subgroup.map_sup]
    refine isZ3E9A4A5_of_commute hA hB ?_
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := hcomm ⟨a, Subgroup.mem_sup_left ha⟩ ⟨b, Subgroup.mem_sup_right hb⟩
    rw [← map_mul, ← map_mul]
    exact congrArg (fun z : ↥(A ⊔ B) => π (z : Λ)) this
  · have hm4 : 4 ≤ m := by rcases hm with rfl | rfl <;> norm_num
    have hinj : Function.Injective (π.comp (A ⊔ B).subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hx1 : π (x : Λ) = 1 := hx
      have hxc : (x : Λ) ∈ Subgroup.center Λ := hker _ hx1
      exact eq_one_of_central_alt hm4 e fun a =>
        Subtype.ext (Subgroup.mem_center_iff.mp hxc (a : Λ))
    have hrange : (π.comp (A ⊔ B).subtype).range = (A ⊔ B).map π := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨(x : Λ), x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    let e' : ↥(A ⊔ B) ≃* ↥((A ⊔ B).map π) :=
      (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
    exact IsZ3E9A4A5.of_mulEquiv e' h

end Central

section Setting

variable {V : Type} [CommGroup V] [Finite V]

structure TenCfg (G T Y : Subgroup (MulAut V)) (t : MulAut V) (L : Subgroup (MulAut V)) :
    Prop where
  cfg : Emb5Cfg G T Y
  hV : ∀ v : V, v ^ 2 = 1
  ht : t ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V))
  ht1 : t ≠ 1
  ht2 : t ^ 2 = 1
  hforall : ∀ g ∈ G, CGT6E.conjSub g Y ⊔ Y ⊔ Subgroup.zpowers t ≠ G
  layer : Emb5Layer G Y L
  hYL : Y ≤ L

variable {G T Y L : Subgroup (MulAut V)} {t : MulAut V}

theorem exists_mul_of_mem_sup {Γ : Type*} [Group Γ] {A B K : Subgroup Γ}
    (hAK : ∀ k ∈ K, ∀ a ∈ A, k * a * k⁻¹ ∈ A) (hBK : B ≤ K) :
    ∀ g ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  let S : Subgroup Γ :=
    { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * (b₁ * a₂ * b₁⁻¹), A.mul_mem ha₁ (hAK b₁ (hBK hb₁) a₂ ha₂), b₁ * b₂,
          B.mul_mem hb₁ hb₂, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨b⁻¹ * a⁻¹ * b⁻¹⁻¹, hAK b⁻¹ (K.inv_mem (hBK hb)) a⁻¹ (A.inv_mem ha), b⁻¹,
          B.inv_mem hb, ?_⟩
        group }
  have : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact fun g hg => this hg

theorem TenCfg.Y_inf_center (hc : TenCfg G T Y t L) {y : MulAut V} (hy : y ∈ Y)
    (hyL : y ∈ L) (hz : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.center ↥L) : y = 1 := by
  by_contra hy1
  have hYz : Subgroup.zpowers y = Y := CGT6E.zpowers_eq_of_card_three hc.cfg.adm.h3 hy hy1
  obtain ⟨y₀, hy₀, x, hx, hxy⟩ := hc.layer.noncentral
  rw [← hYz] at hy₀
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy₀
  apply hxy
  have hcomm : Commute (⟨x, hx⟩ : ↥L) (⟨y, hyL⟩ : ↥L) :=
    (Subgroup.mem_center_iff.mp hz ⟨x, hx⟩)
  have := (hcomm.zpow_right m).eq
  exact congrArg Subtype.val this

theorem TenCfg.card_tilde (hc : TenCfg G T Y t L) : Nat.card ↥(tilde (L := L) Y) = 3 := by
  have hY3 := hc.cfg.adm.h3
  have hinj : Function.Injective ((lpi L).comp (Y.subgroupOf L).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : lpi L (x : ↥L) = 1 := hx
    have hxc : (x : ↥L) ∈ Subgroup.center ↥L := (QuotientGroup.eq_one_iff _).mp hx1
    have hxY : ((x : ↥L) : MulAut V) ∈ Y := Subgroup.mem_subgroupOf.mp x.2
    have := hc.Y_inf_center hxY (x : ↥L).2 (by simpa using hxc)
    exact Subtype.ext (Subtype.ext this)
  have hrange : ((lpi L).comp (Y.subgroupOf L).subtype).range = tilde (L := L) Y := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : ↥L), x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have h1 : Nat.card ↥(Y.subgroupOf L) = 3 := by
    rw [← hY3]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc.hYL).toEquiv
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, h1]

theorem TenCfg.conjSub_le (hc : TenCfg G T Y t L) {l : MulAut V} (hl : l ∈ L) :
    CGT6E.conjSub l Y ≤ L := by
  rintro _ ⟨y, hy, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact L.mul_mem (L.mul_mem hl (hc.hYL hy)) (L.inv_mem hl)

theorem TenCfg.normalClosure_tilde (hc : TenCfg G T Y t L) :
    Subgroup.normalClosure ((tilde (L := L) Y : Subgroup (LQ L)) : Set (LQ L)) = ⊤ := by
  set N' : Subgroup (LQ L) :=
    Subgroup.normalClosure ((tilde (L := L) Y : Subgroup (LQ L)) : Set (LQ L)) with hN'
  have hcc : conjClosure Y G = L := hc.layer.conjClosure_eq hc.hYL
  have hGeq : L ⊔ T = G := hc.cfg.sup_eq_of_le hc.hV hc.layer hc.hYL
  set M' : Subgroup (MulAut V) := (N'.comap (lpi L)).map L.subtype with hM'
  have hS₀ : conjClosure Y G ≤ M' := by
    rw [conjClosure, Subgroup.closure_le]
    rintro _ ⟨g, hg, y, hy, rfl⟩
    have hgLT : g ∈ L ⊔ T := by rw [hGeq]; exact hg
    obtain ⟨l₀, hl₀, t₀, ht₀, rfl⟩ := exists_mul_of_mem_sup (A := L) (B := T) (K := G)
      hc.layer.normal hc.cfg.adm.hTG g hgLT
    have hyt : y * t₀ = t₀ * y :=
      Subgroup.mem_centralizer_iff.mp (hc.cfg.adm.le_centralizer ht₀) y hy
    have e : l₀ * t₀ * y * (l₀ * t₀)⁻¹ = l₀ * y * l₀⁻¹ := by
      calc l₀ * t₀ * y * (l₀ * t₀)⁻¹ = l₀ * (t₀ * y) * t₀⁻¹ * l₀⁻¹ := by group
        _ = l₀ * (y * t₀) * t₀⁻¹ * l₀⁻¹ := by rw [hyt]
        _ = l₀ * y * l₀⁻¹ := by group
    rw [e]
    have hyL : y ∈ L := hc.hYL hy
    have hmem : l₀ * y * l₀⁻¹ ∈ L := L.mul_mem (L.mul_mem hl₀ hyL) (L.inv_mem hl₀)
    refine ⟨⟨l₀ * y * l₀⁻¹, hmem⟩, ?_, rfl⟩
    show lpi L ⟨l₀ * y * l₀⁻¹, hmem⟩ ∈ N'
    have h1 : lpi L ⟨l₀ * y * l₀⁻¹, hmem⟩ =
        lpi L ⟨l₀, hl₀⟩ * lpi L ⟨y, hyL⟩ * (lpi L ⟨l₀, hl₀⟩)⁻¹ := by
      simp only [← map_inv, ← map_mul]
      rfl
    rw [h1]
    exact (Subgroup.normalClosure_normal (s := ((tilde (L := L) Y : Subgroup (LQ L)) :
      Set (LQ L)))).conj_mem _ (Subgroup.subset_normalClosure (mem_tilde.mpr
        ⟨y, hyL, hy, rfl⟩)) _
  rw [eq_top_iff]
  intro s _
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
  have hx : (x : MulAut V) ∈ M' := hS₀ (hcc ▸ x.2)
  obtain ⟨x', hx', hxx⟩ := hx
  have : x' = x := Subtype.ext hxx
  subst this
  exact hx'

omit [Finite V] in
theorem pairGen_eq_sup {Λ : Type} [Group Λ] (A : Subgroup Λ) (g h : Λ) :
    pairGen A g h = A.map (MulAut.conj g).toMonoidHom ⊔ A.map (MulAut.conj h).toMonoidHom := by
  unfold pairGen
  rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]

theorem TenCfg.card_tilde_conj (hc : TenCfg G T Y t L) {l : MulAut V} (hl : l ∈ L) :
    Nat.card ↥(tilde (L := L) (CGT6E.conjSub l Y)) = 3 := by
  rw [← tilde_conj hl]
  rw [Nat.card_congr ((tilde (L := L) Y).equivMapOfInjective _
    (MulAut.conj (lpi L ⟨l, hl⟩)).injective).toEquiv.symm]
  exact hc.card_tilde

theorem TenCfg.pair_tilde (hc : TenCfg G T Y t L) (g h : LQ L) :
    IsZ3E9A4A5 ↥(pairGen (tilde (L := L) Y) g h) := by
  obtain ⟨x₁, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨x₂, rfl⟩ := QuotientGroup.mk_surjective h
  have hx₁ : (x₁ : MulAut V) ∈ G := hc.layer.le x₁.2
  have hx₂ : (x₂ : MulAut V) ∈ G := hc.layer.le x₂.2
  set A := CGT6E.conjSub (x₁ : MulAut V) Y with hA
  set B := CGT6E.conjSub (x₂ : MulAut V) Y with hB
  have hAL : A ≤ L := hc.conjSub_le x₁.2
  have hBL : B ≤ L := hc.conjSub_le x₂.2
  have hpg : pairGen (tilde (L := L) Y) (x₁ : LQ L) (x₂ : LQ L) = tilde (L := L) (A ⊔ B) := by
    rw [pairGen_eq_sup, tilde_sup hAL hBL]
    exact congrArg₂ (· ⊔ ·) (tilde_conj x₁.2) (tilde_conj x₂.2)
  have hJ : IsZ3E9A4A5 ↥(A ⊔ B) := by
    have hg' : (x₁ : MulAut V)⁻¹ * (x₂ : MulAut V) ∈ G := G.mul_mem (G.inv_mem hx₁) hx₂
    have h5 := (hc.cfg.five_nine hc.hV hc.ht hc.ht1 hc.ht2 hg'
      (hc.hforall _ hg')).1
    let φ : MulAut V →* MulAut V := (MulAut.conj (x₁ : MulAut V)).toMonoidHom
    have hmap : (CGT6E.conjSub ((x₁ : MulAut V)⁻¹ * (x₂ : MulAut V)) Y ⊔ Y).map φ = B ⊔ A := by
      rw [Subgroup.map_sup]
      have e1 : (CGT6E.conjSub ((x₁ : MulAut V)⁻¹ * (x₂ : MulAut V)) Y).map φ = B := by
        have := conjSub_conjSub (x₁ : MulAut V) ((x₁ : MulAut V)⁻¹ * (x₂ : MulAut V)) Y
        rw [mul_inv_cancel_left] at this
        exact this
      exact congrArg₂ (· ⊔ ·) e1 rfl
    have e : ↥(CGT6E.conjSub ((x₁ : MulAut V)⁻¹ * (x₂ : MulAut V)) Y ⊔ Y) ≃* ↥(B ⊔ A) :=
      (Subgroup.equivMapOfInjective _ φ (MulAut.conj _).injective).trans
        (MulEquiv.subgroupCongr hmap)
    have h6 := IsZ3E9A4A5.of_mulEquiv e h5
    rw [sup_comm] at h6
    exact h6
  rw [hpg]
  have hsup : (A ⊔ B).subgroupOf L = A.subgroupOf L ⊔ B.subgroupOf L :=
    Subgroup.subgroupOf_sup hAL hBL
  have hJ' : IsZ3E9A4A5 ↥(A.subgroupOf L ⊔ B.subgroupOf L) := by
    rw [← hsup]
    exact IsZ3E9A4A5.of_mulEquiv (Subgroup.subgroupOfEquivOfLe (sup_le hAL hBL)).symm hJ
  have hres := isZ3E9A4A5_map_central (lpi L) (fun x hx => (QuotientGroup.eq_one_iff _).mp hx)
    (A := A.subgroupOf L) (B := B.subgroupOf L) (hc.card_tilde_conj x₁.2)
    (hc.card_tilde_conj x₂.2) hJ'
  rw [← hsup] at hres
  exact hres

theorem TenCfg.exists_alt (K5 : StellmacherSixOneThree) (hc : TenCfg G T Y t L) :
    ∃ n : ℕ, 5 ≤ n ∧ ∃ e : LQ L ≃* alternatingGroup (Fin n), ∃ c : alternatingGroup (Fin n),
      (c : Equiv.Perm (Fin n)).IsThreeCycle ∧
        (tilde (L := L) Y).map e.toMonoidHom = Subgroup.zpowers c := by
  have hq := hc.layer.quasi
  obtain ⟨a, b, hab⟩ := hq.2.2
  exact K5 (LQ L) hq.2.1 ⟨a, b, hab⟩ (tilde (L := L) Y) hc.card_tilde hc.normalClosure_tilde
    hc.pair_tilde

end Setting


end CFSG.CGT.PushingUpLit.CGT6
