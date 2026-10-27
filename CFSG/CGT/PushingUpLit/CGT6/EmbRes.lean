module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCentral
public import CFSG.CGT.PushingUpLit.CGT6.EmbCommV
public import CFSG.CGT.PushingUpLit.CGT6.EmbModDefs
public import CFSG.CGT.PushingUpLit.CGT6.EmbHolTop

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

section Res

variable {V : Type} [CommGroup V]

@[expose] def fixW (W : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | ∀ w ∈ W, g w = w}
  one_mem' := fun w _ => rfl
  mul_mem' := fun {a b} ha hb w hw => by
    show a (b w) = w
    rw [hb w hw, ha w hw]
  inv_mem' := fun {a} ha w hw => by
    have h1 : (a⁻¹ * a) w = w := by simp
    rw [MulAut.mul_apply, ha w hw] at h1
    exact h1

theorem mem_fixW {W : Subgroup V} {g : MulAut V} : g ∈ fixW W ↔ ∀ w ∈ W, g w = w := Iff.rfl

@[expose] def trivQ (W : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | ∀ v : V, g v * v⁻¹ ∈ W}
  one_mem' := fun v => by simp
  mul_mem' := fun {a b} ha hb v => by
    have : (a * b) v * v⁻¹ = (a (b v) * (b v)⁻¹) * (b v * v⁻¹) := by
      simp [MulAut.mul_apply]
    rw [this]
    exact W.mul_mem (ha (b v)) (hb v)
  inv_mem' := fun {a} ha v => by
    have : a⁻¹ v * v⁻¹ = (a (a⁻¹ v) * (a⁻¹ v)⁻¹)⁻¹ := by simp
    rw [this]
    exact W.inv_mem (ha (a⁻¹ v))

theorem mem_trivQ {W : Subgroup V} {g : MulAut V} : g ∈ trivQ W ↔ ∀ v : V, g v * v⁻¹ ∈ W :=
  Iff.rfl

theorem sq_eq_one_of_mem_trivQ_fixW (hV : ∀ v : V, v ^ 2 = 1) {W : Subgroup V} {k : MulAut V}
    (h1 : k ∈ trivQ W) (h2 : k ∈ fixW W) : k ^ 2 = 1 := by
  ext v
  have hw : k v * v⁻¹ ∈ W := h1 v
  have h3 : k (k v * v⁻¹) = k v * v⁻¹ := h2 _ hw
  rw [map_mul, map_inv] at h3
  have hsq : (k ^ 2) v = k (k v) := by simp [pow_two, MulAut.mul_apply]
  rw [hsq]
  have hvv : v * v = 1 := by rw [← pow_two]; exact hV v
  have hxx : k v * k v = 1 := by rw [← pow_two]; exact hV _
  calc k (k v) = (k (k v) * (k v)⁻¹) * k v := (inv_mul_cancel_right _ _).symm
    _ = (k v * v⁻¹) * k v := by rw [h3]
    _ = (k v * k v) * v⁻¹ := mul_right_comm _ _ _
    _ = v⁻¹ := by rw [hxx, one_mul]
    _ = v := inv_eq_of_mul_eq_one_right hvv

theorem commV_le_iff_le_trivQ {W : Subgroup V} {K : Subgroup (MulAut V)} :
    commV K ≤ W ↔ K ≤ trivQ W := by
  constructor
  · intro h g hg v
    exact h (Subgroup.subset_closure ⟨g, hg, v, rfl⟩)
  · intro h
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨g, hg, v, rfl⟩
    exact h hg v

@[expose] noncomputable def resG (G : Subgroup (MulAut V)) (W : Subgroup V) (h : GInv G W) :
    ↥G →* MulAut ↥W where
  toFun g := restrictAut (g : MulAut V) W (h g g.2) (fun w hw => h g⁻¹ (G.inv_mem g.2) w hw)
  map_one' := by
    ext w
    rfl
  map_mul' g g' := by
    ext w
    rfl

variable {G : Subgroup (MulAut V)} {W : Subgroup V} {K : Subgroup (MulAut V)} (h : GInv G W)

theorem resG_apply (g : ↥G) (w : ↥W) :
    ((resG G W h g w : ↥W) : V) = (g : MulAut V) (w : V) := rfl

include h in
theorem mem_ker_resG {g : ↥G} : g ∈ (resG G W h).ker ↔ (g : MulAut V) ∈ fixW W := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg w hw
    have := congrArg (fun φ : MulAut ↥W => ((φ ⟨w, hw⟩ : ↥W) : V)) hg
    simpa [resG_apply] using this
  · intro hg
    ext w
    simpa [resG_apply] using hg (w : V) w.2

@[expose] noncomputable def barW (K : Subgroup (MulAut V)) : Subgroup (MulAut ↥W) :=
  (K.subgroupOf G).map (resG G W h)

include h in
theorem mem_barW {K : Subgroup (MulAut V)} {α : MulAut ↥W} :
    α ∈ barW h K ↔ ∃ g : ↥G, (g : MulAut V) ∈ K ∧ resG G W h g = α := by
  unfold barW
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩

theorem barW_mono {K K' : Subgroup (MulAut V)} (hK : K ≤ K') : barW h K ≤ barW h K' :=
  Subgroup.map_mono (fun _ hx => hK hx)

theorem barW_le_range (K : Subgroup (MulAut V)) : barW h K ≤ (resG G W h).range :=
  Subgroup.map_le_range _ _

theorem barW_self : barW h G = (resG G W h).range := by
  unfold barW
  rw [Subgroup.subgroupOf_self, Subgroup.map_top]

theorem resG_mem_barW {K : Subgroup (MulAut V)} {g : ↥G} (hg : (g : MulAut V) ∈ K) :
    resG G W h g ∈ barW h K :=
  ⟨g, hg, rfl⟩

@[expose] noncomputable def preW (X : Subgroup (MulAut ↥W)) : Subgroup (MulAut V) :=
  (X.comap (resG G W h)).map G.subtype

theorem mem_preW {X : Subgroup (MulAut ↥W)} {x : MulAut V} :
    x ∈ preW h X ↔ ∃ g : ↥G, (g : MulAut V) = x ∧ resG G W h g ∈ X := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, rfl, hg⟩
  · rintro ⟨g, rfl, hg⟩
    exact ⟨g, hg, rfl⟩

theorem resG_mem_of_mem_preW {X : Subgroup (MulAut ↥W)} {x : MulAut V} (hx : x ∈ preW h X)
    (hxG : x ∈ G) : resG G W h ⟨x, hxG⟩ ∈ X := by
  obtain ⟨g, hg, hgX⟩ := (mem_preW h).mp hx
  have : g = ⟨x, hxG⟩ := Subtype.ext hg
  subst this
  exact hgX

theorem preW_mono {X X' : Subgroup (MulAut ↥W)} (hX : X ≤ X') : preW h X ≤ preW h X' :=
  Subgroup.map_mono (Subgroup.comap_mono hX)

theorem preW_le (X : Subgroup (MulAut ↥W)) : preW h X ≤ G := by
  rintro _ ⟨g, _, rfl⟩
  exact g.2

theorem le_preW_barW {K : Subgroup (MulAut V)} (hK : K ≤ G) : K ≤ preW h (barW h K) := by
  intro x hx
  exact (mem_preW h).mpr ⟨⟨x, hK hx⟩, rfl, resG_mem_barW h hx⟩

theorem barW_preW {X : Subgroup (MulAut ↥W)} (hX : X ≤ (resG G W h).range) :
    barW h (preW h X) = X := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨g', hg', hg''⟩ := (mem_preW h).mp hg
    have : g' = g := Subtype.ext hg'
    subst this
    exact hg''
  · intro α hα
    obtain ⟨g, rfl⟩ := hX hα
    exact (mem_barW h).mpr ⟨g, (mem_preW h).mpr ⟨g, rfl, hα⟩, rfl⟩

@[expose] noncomputable def barWEquiv {K : Subgroup (MulAut V)} (hKG : K ≤ G)
    (hinj : K ⊓ fixW W = ⊥) : ↥K ≃* ↥(barW h K) :=
  MulEquiv.ofBijective
    (((resG G W h).comp (Subgroup.inclusion hKG)).codRestrict (barW h K)
      (fun k => resG_mem_barW h (g := ⟨k, hKG k.2⟩) k.2))
    ⟨fun a b hab => by
      have h1 : resG G W h ⟨a, hKG a.2⟩ = resG G W h ⟨b, hKG b.2⟩ := congrArg Subtype.val hab
      have h2 : (⟨a, hKG a.2⟩ : ↥G)⁻¹ * ⟨b, hKG b.2⟩ ∈ (resG G W h).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
      have h3 := (mem_ker_resG h).mp h2
      have h4 : ((a : MulAut V))⁻¹ * (b : MulAut V) ∈ K ⊓ fixW W :=
        ⟨K.mul_mem (K.inv_mem a.2) b.2, h3⟩
      rw [hinj, Subgroup.mem_bot, inv_mul_eq_one] at h4
      exact Subtype.ext h4,
     fun y => by
      obtain ⟨g, hg, hgy⟩ := (mem_barW h).mp y.2
      exact ⟨⟨g, hg⟩, Subtype.ext hgy⟩⟩

theorem coe_barWEquiv {K : Subgroup (MulAut V)} (hKG : K ≤ G) (hinj : K ⊓ fixW W = ⊥)
    (k : ↥K) : ((barWEquiv h hKG hinj k : ↥(barW h K)) : MulAut ↥W) =
      resG G W h ⟨k, hKG k.2⟩ := rfl

@[expose] def commVW (W : Subgroup V) (K : Subgroup (MulAut V)) : Subgroup V :=
  Subgroup.closure {u | ∃ k ∈ K, ∃ w ∈ W, k w * w⁻¹ = u}

theorem commVW_le_commV : commVW W K ≤ commV K := by
  rw [commVW, Subgroup.closure_le]
  rintro _ ⟨k, hk, w, -, rfl⟩
  exact Subgroup.subset_closure ⟨k, hk, w, rfl⟩

theorem mem_commVW {k : MulAut V} (hk : k ∈ K) {w : V} (hw : w ∈ W) : k w * w⁻¹ ∈ commVW W K :=
  Subgroup.subset_closure ⟨k, hk, w, hw, rfl⟩

theorem commVW_le {N : Subgroup V} (hN : ∀ k ∈ K, ∀ w ∈ W, k w * w⁻¹ ∈ N) : commVW W K ≤ N := by
  rw [commVW, Subgroup.closure_le]
  rintro _ ⟨k, hk, w, hw, rfl⟩
  exact hN k hk w hw

theorem commVW_mono_W {W W' : Subgroup V} (hW : W ≤ W') : commVW W K ≤ commVW W' K :=
  commVW_le fun _ hk _ hw => mem_commVW hk (hW hw)

theorem commVW_le_W {K : Subgroup (MulAut V)} (hKW : GInv K W) : commVW W K ≤ W :=
  commVW_le fun k hk w hw => W.mul_mem (hKW k hk w hw) (W.inv_mem hw)

include h in
theorem commV_barW {K : Subgroup (MulAut V)} (hK : K ≤ G) :
    (commV (barW h K)).map W.subtype = commVW W K := by
  unfold commV commVW
  rw [MonoidHom.map_closure]
  congr 1
  ext u
  constructor
  · rintro ⟨_, ⟨α, hα, w, rfl⟩, rfl⟩
    obtain ⟨g, hg, rfl⟩ := (mem_barW h).mp hα
    exact ⟨g, hg, w, w.2, rfl⟩
  · rintro ⟨k, hk, w, hw, rfl⟩
    exact ⟨_, ⟨resG G W h ⟨k, hK hk⟩, resG_mem_barW h hk, ⟨w, hw⟩, rfl⟩, rfl⟩

include h in
theorem mem_commV_barW {K : Subgroup (MulAut V)} (hK : K ≤ G) {w : ↥W} :
    w ∈ commV (barW h K) ↔ (w : V) ∈ commVW W K := by
  rw [← commV_barW h hK]
  exact (Subgroup.mem_map_iff_mem W.subtype_injective).symm

@[expose] def holG (h : GInv G W) : Subgroup (Hol V) where
  carrier := {x | x.left ∈ W ∧ x.right ∈ G}
  one_mem' := ⟨one_mem _, one_mem _⟩
  mul_mem' := by
    rintro ⟨a, α⟩ ⟨b, β⟩ ⟨ha, hα⟩ ⟨hb, hβ⟩
    exact ⟨W.mul_mem ha (h α hα b hb), G.mul_mem hα hβ⟩
  inv_mem' := by
    rintro ⟨a, α⟩ ⟨ha, hα⟩
    exact ⟨h α⁻¹ (G.inv_mem hα) a⁻¹ (W.inv_mem ha), G.inv_mem hα⟩

@[expose] noncomputable def holRes (h : GInv G W) : ↥(holG h) →* Hol ↥W where
  toFun x := ⟨⟨x.1.left, x.2.1⟩, resG G W h ⟨x.1.right, x.2.2⟩⟩
  map_one' := by
    apply SemidirectProduct.ext
    · rfl
    · rfl
  map_mul' x y := by
    apply SemidirectProduct.ext
    · exact Subtype.ext rfl
    · rfl

theorem yuHol_le_holG (hKG : K ≤ G) (hKW : commV K ≤ W) : yuHol K ≤ holG h :=
  fun _ hx => ⟨hKW hx.1, hKG hx.2⟩

@[expose] noncomputable def thetaHol (hKG : K ≤ G) (hKW : commV K ≤ W) :
    ↥(yuHol K) →* Hol ↥W :=
  (holRes h).comp (Subgroup.inclusion (yuHol_le_holG h hKG hKW))

theorem thetaHol_mem (hKG : K ≤ G) (hKW : commV K ≤ W) (hU : commV K ≤ commVW W K)
    (x : ↥(yuHol K)) : thetaHol h hKG hKW x ∈ yuHol (barW h K) :=
  ⟨(mem_commV_barW h hKG).mpr (hU x.2.1), resG_mem_barW h x.2.2⟩

@[expose] noncomputable def thetaK (hKG : K ≤ G) (hKW : commV K ≤ W)
    (hU : commV K ≤ commVW W K) : ↥(yuHol K) →* ↥(yuHol (barW h K)) :=
  (thetaHol h hKG hKW).codRestrict _ (thetaHol_mem h hKG hKW hU)

theorem thetaK_surjective (hKG : K ≤ G) (hKW : commV K ≤ W) (hU : commV K ≤ commVW W K) :
    Function.Surjective (thetaK h hKG hKW hU) := by
  rintro ⟨z, hz⟩
  obtain ⟨g, hg, hgz⟩ := (mem_barW h).mp hz.2
  have hu : ((z.left : ↥W) : V) ∈ commV K := commVW_le_commV
    ((mem_commV_barW h hKG).mp hz.1)
  refine ⟨⟨⟨(z.left : V), (g : MulAut V)⟩, hu, hg⟩, ?_⟩
  apply Subtype.ext
  apply SemidirectProduct.ext
  · exact Subtype.ext rfl
  · exact hgz

theorem mem_ker_thetaK (hKG : K ≤ G) (hKW : commV K ≤ W) (hU : commV K ≤ commVW W K)
    (x : ↥(yuHol K)) :
    x ∈ (thetaK h hKG hKW hU).ker ↔ x.1.left = 1 ∧ x.1.right ∈ fixW W := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have h1 := congrArg (fun z : ↥(yuHol (barW h K)) => (((z : Hol ↥W).left : ↥W) : V)) hx
    have h2 := congrArg (fun z : ↥(yuHol (barW h K)) => (z : Hol ↥W).right) hx
    refine ⟨h1, (mem_ker_resG h (g := ⟨x.1.right, hKG x.2.2⟩)).mp h2⟩
  · rintro ⟨h1, h2⟩
    apply Subtype.ext
    apply SemidirectProduct.ext
    · exact Subtype.ext h1
    · exact (mem_ker_resG h (g := ⟨x.1.right, hKG x.2.2⟩)).mpr h2

theorem shortU_eq_bot_of (hOK : ⁅oTwoIn K, K⁆ = ⊥) : shortU ↥K = ⊥ := by
  have h1 := map_shortU_subtype K
  rw [show blockU K = ⊥ from hOK] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective (shortU ↥K) K.subtype_injective).mp h1

theorem shortU_yuHol_le_ker (hV : ∀ v : V, v ^ 2 = 1) (hOK : ⁅oTwoIn K, K⁆ = ⊥) :
    shortU ↥(yuHol K) ≤ (yuProj K).ker := by
  have hq : TwoQuot (yuProj K) := ⟨yuProj_surjective K, isPGroup_ker_yuProj K hV⟩
  intro x hx
  have h1 : yuProj K x ∈ (shortU ↥(yuHol K)).map (yuProj K) := ⟨x, hx, rfl⟩
  rw [hq.map_shortU, shortU_eq_bot_of hOK, Subgroup.mem_bot] at h1
  exact h1

theorem yuHol_right_pow (x : ↥(yuHol K)) (n : ℕ) :
    ((x ^ n : ↥(yuHol K)) : Hol V).right = ((x : Hol V).right) ^ n := by
  have := map_pow (SemidirectProduct.rightHom : Hol V →* MulAut V) (x : Hol V) n
  simpa using this

include h in
theorem thetaK_centralShort (hV : ∀ v : V, v ^ 2 = 1) (hKG : K ≤ G) (hKW : commV K ≤ W)
    (hU : commV K ≤ commVW W K) (hKC : ∀ k ∈ K ⊓ fixW W, ∀ k' ∈ K, k * k' = k' * k)
    (hK2 : ∀ k ∈ K ⊓ fixW W, ∃ m : ℕ, k ^ 2 ^ m = 1) (hOK : ⁅oTwoIn K, K⁆ = ⊥) :
    CentralShort (thetaK h hKG hKW hU) where
  surj := thetaK_surjective h hKG hKW hU
  two := by
    rintro ⟨x, hx⟩
    have hx' := (mem_ker_thetaK h hKG hKW hU x).mp hx
    obtain ⟨m, hm⟩ := hK2 (x : Hol V).right ⟨x.2.2, hx'.2⟩
    refine ⟨m, ?_⟩
    have hxm : x ^ 2 ^ m ∈ (thetaK h hKG hKW hU).ker := Subgroup.pow_mem _ hx _
    have hxm' := (mem_ker_thetaK h hKG hKW hU _).mp hxm
    apply Subtype.ext
    show x ^ 2 ^ m = 1
    apply Subtype.ext
    apply SemidirectProduct.ext
    · exact hxm'.1
    · rw [yuHol_right_pow, hm]
      rfl
  central := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx' := (mem_ker_thetaK h hKG hKW hU x).mp hx
    apply Subtype.ext
    apply SemidirectProduct.ext
    ·
      have hyl : (y : Hol V).left ∈ W := hKW y.2.1
      have h1 : (x : Hol V).right (y : Hol V).left = (y : Hol V).left := hx'.2 _ hyl
      show (y : Hol V).left * ((y : Hol V).right) ((x : Hol V).left) =
        (x : Hol V).left * ((x : Hol V).right) ((y : Hol V).left)
      rw [hx'.1, h1]
      simp
    · exact (hKC _ ⟨x.2.2, hx'.2⟩ _ y.2.2).symm
  inf_shortU := by
    rw [eq_bot_iff]
    intro x ⟨hx1, hx2⟩
    have hx' := (mem_ker_thetaK h hKG hKW hU x).mp hx1
    have hx'' : x ∈ (yuProj K).ker := shortU_yuHol_le_ker hV hOK hx2
    have hr : (x : Hol V).right = 1 := (mem_ker_yuProj K).mp hx''
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply SemidirectProduct.ext
    · exact hx'.1
    · exact hr

end Res

end CFSG.CGT.PushingUpLit.CGT6
