module

public import CFSG.CGT.PushingUpLit.CGT6.EmbSub
public import CFSG.CGT.PushingUpLit.CGT6.EmbEightFive
public import CFSG.CGT.PushingUpLit.CGT6.Emb5CompY
public import CFSG.CGT.PushingUpLit.CGT6.Emb5FourT

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG

section Twist

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

omit [Finite V] in
theorem noNormalTwo_of_pCore (h : pCore 2 ↥G = ⊥) : NoNormalTwo ↥G := fun _ hN hp =>
  le_bot_iff.mp (h ▸ le_sSup ⟨hN, hp⟩)

theorem Emb5Cfg.twistData (cfg : Emb5Cfg G T Y) {y t : MulAut V} (hy : y ∈ Y) (hy3 : y ^ 3 = 1)
    (ht : t ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V))) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ R : Subgroup ↥G, TwistData (⟨y, (cfg.adm.hYC hy).1⟩ : ↥G) ⟨t, ht.1⟩ R := by
  have hsub := cfg.cent t ht ht1 ht2
  set C : Subgroup (MulAut V) := G ⊓ Subgroup.centralizer ({t} : Set (MulAut V)) with hC
  have hCG : C ≤ G := inf_le_left
  have hYC : Y ≤ C := fun y' hy' =>
    ⟨(cfg.adm.hYC hy').1, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (Subgroup.mem_centralizer_iff.mp ht.2 y' hy').symm⟩
  have hp3 : IsPGroup 3 ↥(Y.subgroupOf C) := by
    have : IsPGroup 3 ↥Y := IsPGroup.of_card (n := 1) (by simpa using cfg.adm.h3)
    exact this.of_equiv (Subgroup.subgroupOfEquivOfLe hYC).symm
  have hle : Y.subgroupOf C ≤ pCore 3 ↥C := le_pCore_of_isSubnormal hsub hp3
  refine ⟨(pCore 3 ↥C).map (Subgroup.inclusion hCG), ?_⟩
  refine ⟨Subtype.ext (by simpa using hy3), Subtype.ext (by simpa using ht2),
    Subtype.ext ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.mem_centralizer_iff.mp ht.2 y hy).symm
  · exact ⟨⟨y, hYC hy⟩, hle (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  · exact (pCore_isPGroup (p := 3) (G := ↥C)).map (Subgroup.inclusion hCG)
  · rintro x hx _ ⟨r, hr, rfl⟩
    have hxC : (x : MulAut V) ∈ C := ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (congrArg Subtype.val hx).symm⟩
    refine ⟨⟨x, hxC⟩ * r * ⟨x, hxC⟩⁻¹,
      (pCore_normal (p := 3) (G := ↥C)).conj_mem r hr ⟨x, hxC⟩, ?_⟩
    simp only [map_mul, map_inv]
    rfl

theorem TwistData.conj {Γ : Type*} [Group Γ] {y t : Γ} {R : Subgroup Γ} (h : TwistData y t R)
    (g : Γ) : TwistData (g * y * g⁻¹) (g * t * g⁻¹) (R.map (MulAut.conj g).toMonoidHom) where
  y3 := by rw [conj_pow, h.y3]; simp
  t2 := by rw [conj_pow, h.t2]; simp
  comm := by
    have := h.comm
    calc g * t * g⁻¹ * (g * y * g⁻¹) = g * (t * y) * g⁻¹ := by group
      _ = g * (y * t) * g⁻¹ := by rw [this]
      _ = g * y * g⁻¹ * (g * t * g⁻¹) := by group
  yR := ⟨y, h.yR, by simp [MulAut.conj_apply]⟩
  R3 := h.R3.map (MulAut.conj g).toMonoidHom
  Rn := by
    rintro x hx _ ⟨r, hr, rfl⟩
    have hx' : (g⁻¹ * x * g) * t = t * (g⁻¹ * x * g) := by
      have e : x * (g * t * g⁻¹) = (g * t * g⁻¹) * x := hx
      calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [e]
        _ = t * (g⁻¹ * x * g) := by group
    refine ⟨(g⁻¹ * x * g) * r * (g⁻¹ * x * g)⁻¹, h.Rn _ hx' r hr, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem Emb5Cfg.normalizes_conj (cfg : Emb5Cfg G T Y) {y t : MulAut V} (hy : y ∈ Y)
    (hy3 : y ^ 3 = 1) (ht : t ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V))) (ht1 : t ≠ 1)
    (ht2 : t ^ 2 = 1) {L : Subgroup ↥G} (hL : CFSG.IsComponent L) (g : ↥G) :
    g * ⟨y, (cfg.adm.hYC hy).1⟩ * g⁻¹ ∈ Subgroup.normalizer (L : Set ↥G) := by
  obtain ⟨R, hR⟩ := cfg.twistData hy hy3 ht ht1 ht2
  exact (hR.conj g).normalizes (noNormalTwo_of_pCore cfg.o2) hL

end Twist

section Normal

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

omit [Finite V] in
theorem mem_map_subtype_mul {g y' : MulAut V} (hg : g ∈ G) (hy : y' ∈ G) (N : Subgroup ↥G)
    (h : (⟨g, hg⟩ * ⟨y', hy⟩ * ⟨g, hg⟩⁻¹ : ↥G) ∈ N) : g * y' * g⁻¹ ∈ N.map G.subtype :=
  Subgroup.mem_map.mpr ⟨_, h, by simp⟩

theorem Emb5Cfg.sec5 (cfg : Emb5Cfg G T Y) (hV : ∀ v : V, v ^ 2 = 1) : Sec5Hyp V G T Y :=
  ⟨hV, cfg.adm.hTG, cfg.adm.hT2, cfg.adm.hYC, cfg.adm.hsub, cfg.adm.h3, cfg.adm.h4⟩

theorem Emb5Cfg.not_isPGroup_Y (cfg : Emb5Cfg G T Y) : ¬ IsPGroup 2 ↥Y :=
  not_isPGroup_two_of_card_three cfg.adm.h3

theorem Lift5.up {K X : Subgroup (MulAut V)} (hYG : Y ≤ G) (hY2 : ¬ IsPGroup 2 ↥Y)
    (hNK : conjClosure Y G ≤ K) (hKG : K ≤ G) (h : Lift5 K Y X) : Lift5 G Y X := by
  have hcc : conjClosure Y X = X := Lift5.conjClosure_eq hY2 h
  obtain ⟨hYX, hXK, hsub, hc, harr⟩ := h
  exact ⟨hYX, hXK.trans hKG,
    isSubnormal_of_conjClosure hYG hNK hcc (hXK.trans hKG) hsub, hc, harr⟩

theorem Emb5Cfg.normal_of_component (cfg : Emb5Cfg G T Y) (hV : ∀ v : V, v ^ 2 = 1)
    {L : Subgroup ↥G} (hL : CFSG.IsComponent L) {y : MulAut V} (hy : y ∈ Y)
    {l : ↥G} (hl : l ∈ L) (hne : l * ⟨y, (cfg.adm.hYC hy).1⟩ ≠ ⟨y, (cfg.adm.hYC hy).1⟩ * l) :
    L.Normal := by
  have hsec := cfg.sec5 hV
  obtain ⟨z, hzT, hz1, hz2, -⟩ := exists_central_involution cfg.adm.hT1 cfg.adm.hT2
  have hzG : z ∈ G := cfg.adm.hTG hzT
  have hzC : z ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)) :=
    ⟨hzG, cfg.adm.le_centralizer hzT⟩
  have hYG : Y ≤ G := fun y' hy' => (cfg.adm.hYC hy').1
  have hy3 : y ^ 3 = 1 := hsec.pow_three hy
  have hnorm : ∀ (y' : MulAut V) (hy' : y' ∈ Y) (g : ↥G),
      g * ⟨y', (cfg.adm.hYC hy').1⟩ * g⁻¹ ∈ Subgroup.normalizer (L : Set ↥G) :=
    fun y' hy' g => cfg.normalizes_conj hy' (hsec.pow_three hy') hzC hz1 hz2 hL g
  obtain ⟨R, hR⟩ := cfg.twistData hy hy3 hzC hz1 hz2
  have hyL : (⟨y, (cfg.adm.hYC hy).1⟩ : ↥G) ∈ Subgroup.normalizer (L : Set ↥G) := by
    have := hnorm y hy 1
    rwa [one_mul, inv_one, mul_one] at this
  have hzL : (⟨z, hzG⟩ : ↥G) ∈ Subgroup.normalizer (L : Set ↥G) :=
    hR.normalizes_t hL hyL ⟨l, hl, hne⟩
  set K : Subgroup (MulAut V) := (Subgroup.normalizer (L : Set ↥G)).map G.subtype with hK
  have hKG : K ≤ G := Subgroup.map_subtype_le _
  have hNK : conjClosure Y G ≤ K := by
    rw [conjClosure, Subgroup.closure_le]
    rintro _ ⟨g, hg, y', hy', rfl⟩
    exact mem_map_subtype_mul hg (cfg.adm.hYC hy').1 _ (hnorm y' hy' ⟨g, hg⟩)
  have hzK : z ∈ K := ⟨⟨z, hzG⟩, hzL, rfl⟩
  have hKeq : K = G := by
    by_contra hKne
    have hlt : K < G := lt_of_le_of_ne hKG hKne
    have hadm : Adm5 K (Subgroup.zpowers z) Y :=
      { hTG := Subgroup.zpowers_le.mpr hzK
        hT1 := zpowers_ne_bot hz1
        hT2 := isPGroup_zpowers_of_sq hz2
        hYC := by
          refine fun y' hy' => ⟨le_conjClosure.trans hNK hy', ?_⟩
          rw [centralizer_zpowers_eq]
          exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
            rw [Set.mem_singleton_iff] at hh
            subst hh
            exact (Subgroup.mem_centralizer_iff.mp hzC.2 y' hy').symm
        hsub := by
          have hcent := cfg.cent z hzC hz1 hz2
          rw [centralizer_zpowers_eq]
          refine CFSG.GroupTheory.isSubnormal_subgroupOf_of_le (inf_le_inf_right _ hKG) hcent
        h3 := cfg.adm.h3
        h4 := cfg.adm.h4 }
    obtain ⟨X, hX⟩ := cfg.lift_sub hV hlt hadm
    exact cfg.nolift ⟨X, Lift5.up hYG cfg.not_isPGroup_Y hNK hKG hX⟩
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
  intro x _
  have hx : (x : MulAut V) ∈ K := by
    rw [hKeq]
    exact x.2
  obtain ⟨n, hn, hnx⟩ := hx
  have : n = x := Subtype.ext hnx
  rwa [← this]

end Normal

end CFSG.CGT.PushingUpLit.CGT6
