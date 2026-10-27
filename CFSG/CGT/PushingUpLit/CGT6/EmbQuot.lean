module

public import CFSG.CGT.PushingUpLit.CGT6.EmbRes
public import CFSG.CGT.PushingUpLit.CGT6.EmbEightFive

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
open scoped commutatorElement

section Gen

variable {M Γ : Type*} [Group M] [Group Γ] {G : Subgroup M} (ρ : ↥G →* Γ)

@[expose] def homImg (K : Subgroup M) : Subgroup Γ :=
  (K.subgroupOf G).map ρ

@[expose] def homPre (X : Subgroup Γ) : Subgroup M :=
  (X.comap ρ).map G.subtype

variable {ρ}

theorem mem_homImg {K : Subgroup M} {x : Γ} :
    x ∈ homImg ρ K ↔ ∃ g : ↥G, (g : M) ∈ K ∧ ρ g = x := by
  unfold homImg
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩

theorem homImg_mono {K K' : Subgroup M} (hK : K ≤ K') : homImg ρ K ≤ homImg ρ K' :=
  Subgroup.map_mono (fun _ hx => hK hx)

theorem homImg_self : homImg ρ G = ρ.range := by
  unfold homImg
  rw [Subgroup.subgroupOf_self, Subgroup.map_top]

theorem hom_mem_homImg {K : Subgroup M} {g : ↥G} (hg : (g : M) ∈ K) : ρ g ∈ homImg ρ K :=
  ⟨g, hg, rfl⟩

theorem mem_homPre {X : Subgroup Γ} {x : M} :
    x ∈ homPre ρ X ↔ ∃ g : ↥G, (g : M) = x ∧ ρ g ∈ X := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, rfl, hg⟩
  · rintro ⟨g, rfl, hg⟩
    exact ⟨g, hg, rfl⟩

theorem homPre_mono {X X' : Subgroup Γ} (hX : X ≤ X') : homPre ρ X ≤ homPre ρ X' :=
  Subgroup.map_mono (Subgroup.comap_mono hX)

theorem homPre_le (X : Subgroup Γ) : homPre ρ X ≤ G := by
  rintro _ ⟨g, _, rfl⟩
  exact g.2

theorem le_homPre_homImg {K : Subgroup M} (hK : K ≤ G) : K ≤ homPre ρ (homImg ρ K) := by
  intro x hx
  exact mem_homPre.mpr ⟨⟨x, hK hx⟩, rfl, hom_mem_homImg hx⟩

theorem homImg_homPre {X : Subgroup Γ} (hX : X ≤ ρ.range) : homImg ρ (homPre ρ X) = X := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨g', hg', hg''⟩ := mem_homPre.mp hg
    have : g' = g := Subtype.ext hg'
    subst this
    exact hg''
  · intro α hα
    obtain ⟨g, rfl⟩ := hX hα
    exact mem_homImg.mpr ⟨g, mem_homPre.mpr ⟨g, rfl, hα⟩, rfl⟩

@[expose] noncomputable def homImgEquiv (hρ : Function.Injective ρ) {K : Subgroup M}
    (hKG : K ≤ G) : ↥K ≃* ↥(homImg ρ K) :=
  MulEquiv.ofBijective
    ((ρ.comp (Subgroup.inclusion hKG)).codRestrict (homImg ρ K)
      (fun k => hom_mem_homImg (ρ := ρ) (g := ⟨k, hKG k.2⟩) k.2))
    ⟨fun a b hab => by
      have h1 : ρ ⟨a, hKG a.2⟩ = ρ ⟨b, hKG b.2⟩ := congrArg Subtype.val hab
      have h2 := hρ h1
      exact Subtype.ext (show (a : M) = b from congrArg (fun x : ↥G => (x : M)) h2),
     fun y => by
      obtain ⟨g, hg, hgy⟩ := mem_homImg.mp y.2
      exact ⟨⟨g, hg⟩, Subtype.ext hgy⟩⟩

theorem homPre_homImg (hρ : Function.Injective ρ) {K : Subgroup M} (hKG : K ≤ G) :
    homPre ρ (homImg ρ K) = K := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, hg, hgK⟩ := mem_homPre.mp hx
    obtain ⟨g', hg', hg'g⟩ := mem_homImg.mp hgK
    have : g' = g := hρ hg'g
    subst this
    rw [← hg]
    exact hg'
  · exact le_homPre_homImg hKG

theorem card_homImg_self (hρ : Function.Injective ρ) :
    Nat.card ↥(homImg ρ G) = Nat.card ↥G :=
  (Nat.card_congr (homImgEquiv hρ (le_refl G)).toEquiv).symm

theorem homImg_commutator {A B : Subgroup M} (hA : A ≤ G) (hB : B ≤ G) :
    ⁅homImg ρ A, homImg ρ B⁆ = homImg ρ ⁅A, B⁆ := by
  have hAB : ⁅A, B⁆ ≤ G := (Subgroup.commutator_mono hA hB).trans (Subgroup.commutator_le_self _)
  have key : ⁅A.subgroupOf G, B.subgroupOf G⁆ = (⁅A, B⁆).subgroupOf G := by
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
      Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hAB]
  unfold homImg
  rw [← Subgroup.map_commutator, key]

theorem isPGroup_homImg {p : ℕ} {T : Subgroup M} (hTG : T ≤ G) (hT : IsPGroup p ↥T) :
    IsPGroup p ↥(homImg ρ T) :=
  (IsPGroup.of_surjective hT (Subgroup.subgroupOfEquivOfLe hTG).symm.toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hTG).symm.surjective).map _

theorem homImg_le_centralizer {T Y : Subgroup M} (hYG : Y ≤ G)
    (hYT : Y ≤ Subgroup.centralizer (T : Set M)) :
    homImg ρ Y ≤ homImg ρ G ⊓ Subgroup.centralizer (homImg ρ T : Set Γ) := by
  refine le_inf (homImg_mono hYG) ?_
  intro yb hyb
  rw [Subgroup.mem_centralizer_iff]
  intro tb htb
  obtain ⟨y, hy, rfl⟩ := mem_homImg.mp hyb
  obtain ⟨t, ht, rfl⟩ := mem_homImg.mp htb
  have : (t : M) * (y : M) = (y : M) * (t : M) :=
    Subgroup.mem_centralizer_iff.mp (hYT hy) _ ht
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext this

theorem isSubnormal_homImg {A Y : Subgroup M} (hYA : Y ≤ A) (hAG : A ≤ G)
    (hsub : (Y.subgroupOf A).IsSubnormal) :
    ((homImg ρ Y).subgroupOf (homImg ρ A)).IsSubnormal := by
  let f : ↥A →* ↥(homImg ρ A) :=
    (ρ.comp (Subgroup.inclusion hAG)).codRestrict (homImg ρ A)
      (fun a => hom_mem_homImg (ρ := ρ) (g := ⟨a, hAG a.2⟩) a.2)
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨g, hg, rfl⟩ := mem_homImg.mp hz
    exact ⟨⟨g, hg⟩, rfl⟩
  have h1 := hsub.map hf
  convert h1 using 1
  ext z
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · intro hz
    obtain ⟨g, hg, hgz⟩ := mem_homImg.mp hz
    refine ⟨⟨g, hYA hg⟩, hg, ?_⟩
    exact Subtype.ext hgz
  · rintro ⟨a, ha, rfl⟩
    exact hom_mem_homImg (ρ := ρ) (g := ⟨a, hAG a.2⟩) ha

theorem homImg_inf_centralizer (hρ : Function.Injective ρ) {T : Subgroup M} (hTG : T ≤ G) :
    homImg ρ (G ⊓ Subgroup.centralizer (T : Set M)) =
      homImg ρ G ⊓ Subgroup.centralizer (homImg ρ T : Set Γ) := by
  apply le_antisymm
  · refine le_inf (homImg_mono inf_le_left) ?_
    intro x hx
    obtain ⟨g, hg, rfl⟩ := mem_homImg.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro tb htb
    obtain ⟨t, ht, rfl⟩ := mem_homImg.mp htb
    have : (t : M) * (g : M) = (g : M) * (t : M) :=
      Subgroup.mem_centralizer_iff.mp hg.2 _ ht
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext this
  · rintro x ⟨hxG, hxC⟩
    obtain ⟨g, hg, rfl⟩ := mem_homImg.mp hxG
    refine mem_homImg.mpr ⟨g, ⟨hg, Subgroup.mem_centralizer_iff.mpr ?_⟩, rfl⟩
    intro t ht
    have h1 := Subgroup.mem_centralizer_iff.mp hxC (ρ ⟨t, hTG ht⟩)
      (hom_mem_homImg (g := ⟨t, hTG ht⟩) ht)
    rw [← map_mul, ← map_mul] at h1
    have h2 := hρ h1
    exact congrArg Subtype.val h2

end Gen

section Quot

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {A : Subgroup V}

theorem map_eq_of_ginv (h : GInv G A) (g : ↥G) :
    A.map ((g : MulAut V) : V →* V) = A := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact h g g.2 a ha
  · intro a ha
    refine ⟨(g : MulAut V)⁻¹ a, h g⁻¹ (G.inv_mem g.2) a ha, ?_⟩
    simp

@[expose] noncomputable def resQ (G : Subgroup (MulAut V)) (A : Subgroup V) (h : GInv G A) :
    ↥G →* MulAut (V ⧸ A) where
  toFun g := QuotientGroup.congr A A (g : MulAut V) (map_eq_of_ginv h g)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' g g' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem resQ_mk (h : GInv G A) (g : ↥G) (v : V) :
    resQ G A h g (v : V ⧸ A) = (((g : MulAut V) v : V) : V ⧸ A) := rfl

theorem mem_ker_resQ (h : GInv G A) {g : ↥G} :
    g ∈ (resQ G A h).ker ↔ (g : MulAut V) ∈ trivQ A := by
  rw [MonoidHom.mem_ker, mem_trivQ]
  constructor
  · intro hg v
    have h1 := congrArg (fun φ : MulAut (V ⧸ A) => φ (v : V ⧸ A)) hg
    simp only [resQ_mk, MulAut.one_apply] at h1
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1]
    exact mul_inv_cancel _
  · intro hg
    ext x
    induction x using QuotientGroup.induction_on with
    | H v =>
      rw [resQ_mk]
      simp only [MulAut.one_apply]
      rw [QuotientGroup.eq]
      have := A.inv_mem (hg v)
      rwa [mul_inv_rev, inv_inv, mul_comm] at this

structure QData (G : Subgroup (MulAut V)) (A : Subgroup V) : Prop where
  fix : ∀ g ∈ G, ∀ a ∈ A, g a = a
  inj : G ⊓ trivQ A = ⊥
  card : Nat.card ↥A ≤ 2

theorem QData.inv (D : QData G A) : GInv G A := fun g hg a ha => by
  rw [D.fix g hg a ha]
  exact ha

theorem QData.resQ_injective (D : QData G A) : Function.Injective (resQ G A D.inv) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : (g : MulAut V) ∈ G ⊓ trivQ A :=
    ⟨g.2, (mem_ker_resQ D.inv).mp (MonoidHom.mem_ker.mpr hg)⟩
  rw [D.inj, Subgroup.mem_bot] at h1
  exact Subtype.ext h1

@[expose, reducible] noncomputable def barQ (h : GInv G A) (K : Subgroup (MulAut V)) :
    Subgroup (MulAut (V ⧸ A)) :=
  homImg (resQ G A h) K

@[expose, reducible] noncomputable def preQ (h : GInv G A) (X : Subgroup (MulAut (V ⧸ A))) :
    Subgroup (MulAut V) :=
  homPre (resQ G A h) X

end Quot

section Faithful

variable {V : Type} [CommGroup V]

theorem normalizer_trivQ_of_ginv {G : Subgroup (MulAut V)} {W : Subgroup V} (h : GInv G W) :
    G ≤ Subgroup.normalizer (trivQ W : Set (MulAut V)) := by
  have key : ∀ g ∈ G, ∀ x ∈ trivQ W, g * x * g⁻¹ ∈ trivQ W := by
    intro g hg x hx v
    have h1 : (g * x * g⁻¹) v * v⁻¹ = g (x (g⁻¹ v) * (g⁻¹ v)⁻¹) := by
      simp [MulAut.mul_apply]
    rw [h1]
    exact h g hg _ (hx _)
  intro g hg
  exact mem_normalizer_of_conj_mem (key g hg) (fun x hx => by
    simpa using key g⁻¹ (G.inv_mem hg) x hx)

theorem normalizer_fixW_of_ginv {G : Subgroup (MulAut V)} {W : Subgroup V} (h : GInv G W) :
    G ≤ Subgroup.normalizer (fixW W : Set (MulAut V)) := by
  have key : ∀ g ∈ G, ∀ x ∈ fixW W, g * x * g⁻¹ ∈ fixW W := by
    intro g hg x hx w hw
    have h1 : g⁻¹ w ∈ W := h g⁻¹ (G.inv_mem hg) w hw
    show g (x (g⁻¹ w)) = w
    rw [hx _ h1]
    simp
  intro g hg
  exact mem_normalizer_of_conj_mem (key g hg) (fun x hx => by
    simpa using key g⁻¹ (G.inv_mem hg) x hx)

theorem inf_fixW_trivQ_le_oTwoIn_of_ginv [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G : Subgroup (MulAut V)} {W : Subgroup V} (h : GInv G W) :
    G ⊓ fixW W ⊓ trivQ W ≤ oTwoIn G := by
  have hnorm : G ≤ Subgroup.normalizer
      ((G ⊓ fixW W ⊓ trivQ W : Subgroup (MulAut V)) : Set (MulAut V)) := by
    have h1 : G ≤ Subgroup.normalizer ((G ⊓ fixW W : Subgroup (MulAut V)) : Set (MulAut V)) :=
      le_trans (le_inf Subgroup.le_normalizer (normalizer_fixW_of_ginv h))
        Subgroup.inf_normalizer_le_normalizer_inf
    exact le_trans (le_inf h1 (normalizer_trivQ_of_ginv h))
      Subgroup.inf_normalizer_le_normalizer_inf
  exact le_oTwoIn_of_normal (inf_le_left.trans inf_le_left) hnorm
    (fun x => ⟨1, Subtype.ext (by
      simpa using sq_eq_one_of_mem_trivQ_fixW hV x.2.2 x.2.1.2)⟩)

theorem QData.of_oTwoIn_eq_bot [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)}
    {A : Subgroup V} (hfix : ∀ g ∈ G, ∀ a ∈ A, g a = a) (hcard : Nat.card ↥A ≤ 2)
    (hO : oTwoIn G = ⊥) : QData G A where
  fix := hfix
  inj := by
    rw [eq_bot_iff]
    intro g hg
    have hinv : GInv G A := fun g hg a ha => by
      rw [hfix g hg a ha]
      exact ha
    have hmem : g ∈ G ⊓ fixW A ⊓ trivQ A := ⟨⟨hg.1, fun w hw => hfix g hg.1 w hw⟩, hg.2⟩
    have := inf_fixW_trivQ_le_oTwoIn_of_ginv hV hinv hmem
    rw [hO, Subgroup.mem_bot] at this
    exact this
  card := hcard

end Faithful

section Theta

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {A : Subgroup V} (h : GInv G A)
  {K : Subgroup (MulAut V)}

include h in
theorem commV_barQ (hKG : K ≤ G) :
    (commV K).map (QuotientGroup.mk' A) = commV (barQ h K) := by
  unfold commV
  rw [MonoidHom.map_closure]
  congr 1
  ext u
  constructor
  · rintro ⟨_, ⟨k, hk, v, rfl⟩, rfl⟩
    exact ⟨resQ G A h ⟨k, hKG hk⟩, hom_mem_homImg (ρ := resQ G A h) (g := ⟨k, hKG hk⟩) hk,
      (v : V ⧸ A), rfl⟩
  · rintro ⟨α, hα, w, rfl⟩
    obtain ⟨g, hg, rfl⟩ := mem_homImg.mp hα
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective w
    exact ⟨_, ⟨g, hg, v, rfl⟩, rfl⟩

@[expose] noncomputable def thetaQHol (hKG : K ≤ G) : ↥(yuHol K) →* Hol (V ⧸ A) where
  toFun x := ⟨((x.1.left : V) : V ⧸ A), resQ G A h ⟨x.1.right, hKG x.2.2⟩⟩
  map_one' := by
    apply SemidirectProduct.ext
    · rfl
    · exact map_one (resQ G A h)
  map_mul' x y := by
    apply SemidirectProduct.ext
    · rfl
    · show resQ G A h ⟨((x * y : ↥(yuHol K)) : Hol V).right, hKG (x * y).2.2⟩ =
        resQ G A h ⟨(x : Hol V).right, hKG x.2.2⟩ * resQ G A h ⟨(y : Hol V).right, hKG y.2.2⟩
      rw [← map_mul]
      rfl

theorem thetaQHol_left (hKG : K ≤ G) (x : ↥(yuHol K)) :
    (thetaQHol h hKG x).left = ((x.1.left : V) : V ⧸ A) := rfl

theorem thetaQHol_right (hKG : K ≤ G) (x : ↥(yuHol K)) :
    (thetaQHol h hKG x).right = resQ G A h ⟨x.1.right, hKG x.2.2⟩ := rfl

theorem thetaQHol_mem (hKG : K ≤ G) (x : ↥(yuHol K)) :
    thetaQHol h hKG x ∈ yuHol (barQ h K) :=
  ⟨by
    rw [← commV_barQ h hKG]
    exact ⟨x.1.left, x.2.1, rfl⟩,
   hom_mem_homImg (ρ := resQ G A h) (g := ⟨x.1.right, hKG x.2.2⟩) x.2.2⟩

@[expose] noncomputable def thetaQ (hKG : K ≤ G) : ↥(yuHol K) →* ↥(yuHol (barQ h K)) :=
  (thetaQHol h hKG).codRestrict _ (thetaQHol_mem h hKG)

theorem coe_thetaQ (hKG : K ≤ G) (x : ↥(yuHol K)) :
    ((thetaQ h hKG x : ↥(yuHol (barQ h K))) : Hol (V ⧸ A)) = thetaQHol h hKG x := rfl

theorem thetaQ_surjective (hKG : K ≤ G) : Function.Surjective (thetaQ h hKG) := by
  rintro ⟨z, hz⟩
  have hl : z.left ∈ commV (barQ h K) := hz.1
  rw [← commV_barQ h hKG] at hl
  obtain ⟨u, hu, hzu⟩ := hl
  obtain ⟨g, hg, hgz⟩ := mem_homImg.mp hz.2
  refine ⟨⟨⟨u, (g : MulAut V)⟩, hu, hg⟩, ?_⟩
  apply Subtype.ext
  apply SemidirectProduct.ext
  · exact hzu
  · exact hgz

theorem mem_ker_thetaQ (hKG : K ≤ G) (x : ↥(yuHol K)) :
    x ∈ (thetaQ h hKG).ker ↔
      x.1.left ∈ A ∧ resQ G A h ⟨x.1.right, hKG x.2.2⟩ = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have h1 := congrArg (fun z : ↥(yuHol (barQ h K)) => (z : Hol (V ⧸ A)).left) hx
    have h2 := congrArg (fun z : ↥(yuHol (barQ h K)) => (z : Hol (V ⧸ A)).right) hx
    refine ⟨?_, h2⟩
    rw [← QuotientGroup.eq_one_iff]
    exact h1
  · rintro ⟨h1, h2⟩
    apply Subtype.ext
    apply SemidirectProduct.ext
    · exact (QuotientGroup.eq_one_iff _).mpr h1
    · exact h2

theorem thetaQ_centralTwoQuot (hV : ∀ v : V, v ^ 2 = 1) (D : QData G A) (hKG : K ≤ G) :
    CentralTwoQuot (thetaQ D.inv hKG) := by
  have hright : ∀ x : ↥(yuHol K), x ∈ (thetaQ D.inv hKG).ker → x.1.right = 1 := by
    intro x hx
    have hx' := (mem_ker_thetaQ D.inv hKG x).mp hx
    have h1 : (x.1.right : MulAut V) ∈ G ⊓ trivQ A :=
      ⟨hKG x.2.2, (mem_ker_resQ D.inv (g := ⟨x.1.right, hKG x.2.2⟩)).mp
        (MonoidHom.mem_ker.mpr hx'.2)⟩
    rw [D.inj, Subgroup.mem_bot] at h1
    exact h1
  refine ⟨⟨thetaQ_surjective D.inv hKG, ?_⟩, ?_⟩
  · rintro ⟨x, hx⟩
    refine ⟨1, ?_⟩
    have hr := hright x hx
    have hxx : ((x : Hol V) * (x : Hol V)) = 1 := by
      apply SemidirectProduct.ext
      · show (x : Hol V).left * (x : Hol V).right (x : Hol V).left = 1
        rw [hr]
        show (x : Hol V).left * (x : Hol V).left = 1
        rw [← pow_two]
        exact hV _
      · show (x : Hol V).right * (x : Hol V).right = 1
        rw [hr, one_mul]
    rw [pow_one, pow_two]
    apply Subtype.ext
    apply Subtype.ext
    exact hxx
  · intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hr := hright x hx
    have hl := ((mem_ker_thetaQ D.inv hKG x).mp hx).1
    apply Subtype.ext
    apply SemidirectProduct.ext
    · show (y : Hol V).left * (y : Hol V).right (x : Hol V).left =
        (x : Hol V).left * (x : Hol V).right (y : Hol V).left
      rw [hr, D.fix _ (hKG y.2.2) _ hl]
      show (y : Hol V).left * (x : Hol V).left = (x : Hol V).left * (1 : MulAut V) (y : Hol V).left
      rw [MulAut.one_apply, mul_comm]
    · show (y : Hol V).right * (x : Hol V).right = (x : Hol V).right * (y : Hol V).right
      rw [hr, one_mul, mul_one]

end Theta

end CFSG.CGT.PushingUpLit.CGT6
