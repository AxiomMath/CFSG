module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenGeneric
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionLift

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

section Abstract

theorem exists_projection_surjective {W Y K : Type*} [Group W] [Group Y] [Group K]
    (ψ : W →* K) (ρ : W →* Y) (K₀ : Subgroup Y) [hK₀ : K₀.Normal]
    (hZ : Subgroup.center K₀ = ⊥) (P : Subgroup W) (hPψ : P.map ψ = ⊤)
    (hPρ : P.map ρ ≤ K₀ ⊔ Subgroup.centralizer (K₀ : Set Y)) (X : Subgroup K)
    (hX : ∀ T : Subgroup K, T.Normal → T ≤ X → T = ⊥)
    (hPX : ∀ x ∈ P, ρ x ∈ Subgroup.centralizer (K₀ : Set Y) → ψ x ∈ X) :
    ∃ U : Subgroup K₀, (∃ φ : U →* K, Function.Surjective φ) ∧
      ∀ u ∈ U, ∃ x ∈ P, (u : Y) * (ρ x)⁻¹ ∈ Subgroup.centralizer (K₀ : Set Y) := by
  set C := Subgroup.centralizer (K₀ : Set Y)
  have hcomm : ∀ (a : K₀) (c : C), Commute (K₀.subtype a) (C.subtype c) := fun a c =>
    Subgroup.mem_centralizer_iff.mp c.2 a a.2
  have hdisj : Disjoint K₀.subtype.range C.subtype.range := by
    rw [Subgroup.range_subtype, Subgroup.range_subtype, Subgroup.disjoint_def]
    intro x hxK hxC
    have hx : (⟨x, hxK⟩ : K₀) ∈ Subgroup.center K₀ := Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC g g.2)
    rw [hZ, Subgroup.mem_bot] at hx
    exact congrArg Subtype.val hx
  set e := MonoidHom.noncommCoprod K₀.subtype C.subtype hcomm with he
  have hinj : Function.Injective e := (MonoidHom.noncommCoprod_injective _ _ hcomm).mpr
    ⟨K₀.subtype_injective, C.subtype_injective, hdisj⟩
  have hrange : e.range = K₀ ⊔ C := by
    rw [he, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hρe : ∀ x : P, ρ x ∈ e.range := fun x => hrange ▸ hPρ (Subgroup.mem_map_of_mem ρ x.2)
  set Φ : P →* K₀ × C := (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp
    ((ρ.comp P.subtype).codRestrict e.range hρe)
  have hΦ : ∀ x : P, ρ x = ((Φ x).1 : Y) * ((Φ x).2 : Y) := by
    intro x
    have h1 : MonoidHom.ofInjective hinj (Φ x) =
        (ρ.comp P.subtype).codRestrict e.range hρe x := MulEquiv.apply_symm_apply _ _
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    rw [← show (ρ.comp P.subtype).codRestrict e.range hρe x = ρ x from rfl, ← h2, he,
      MonoidHom.noncommCoprod_apply]
    rfl
  set σ : P →* K₀ := (MonoidHom.fst K₀ C).comp Φ
  set W₂ : Subgroup W := P ⊓ C.comap ρ
  have hTn : (W₂.map ψ).Normal := by
    refine ⟨fun t ht k => ?_⟩
    obtain ⟨w, hw, rfl⟩ := ht
    obtain ⟨x, hx, rfl⟩ : k ∈ P.map ψ := hPψ ▸ Subgroup.mem_top k
    refine ⟨x * w * x⁻¹, ⟨P.mul_mem (P.mul_mem hx hw.1) (P.inv_mem hx), ?_⟩, by
      rw [map_mul, map_mul, map_inv]⟩
    show ρ (x * w * x⁻¹) ∈ C
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.normal_centralizer (H := K₀)).conj_mem _ hw.2 _
  have hT : W₂.map ψ = ⊥ := hX _ hTn (by
    rintro _ ⟨w, hw, rfl⟩
    exact hPX w hw.1 hw.2)
  set ψP : P →* K := ψ.comp P.subtype
  have hψPs : Function.Surjective ψP := by
    intro k
    obtain ⟨x, hx, rfl⟩ : k ∈ P.map ψ := hPψ ▸ Subgroup.mem_top k
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : σ.rangeRestrict.ker ≤ ψP.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have h1 : (Φ x).1 = 1 := hx
    have hρC : ρ x ∈ C := by
      rw [hΦ x, h1, OneMemClass.coe_one, one_mul]
      exact (Φ x).2.2
    have hψ : ψP x ∈ W₂.map ψ := ⟨x, ⟨x.2, hρC⟩, rfl⟩
    rwa [hT, Subgroup.mem_bot] at hψ
  obtain ⟨φ, -, hφs, -⟩ := CFSG.AGLEmbedding.exists_surjective_comp_eq σ.rangeRestrict
    σ.rangeRestrict_surjective ψP hψPs hker
  refine ⟨σ.range, ⟨φ, hφs⟩, ?_⟩
  rintro u ⟨x, rfl⟩
  refine ⟨x, x.2, ?_⟩
  have hac : ((Φ x).2 : Y) * ((Φ x).1 : Y) = ((Φ x).1 : Y) * ((Φ x).2 : Y) :=
    (Subgroup.mem_centralizer_iff.mp (Φ x).2.2 _ (Φ x).1.2).symm
  have e1 : ((σ x : K₀) : Y) * (ρ x)⁻¹ = ((Φ x).2 : Y)⁻¹ := by
    rw [hΦ x, ← hac]
    show ((Φ x).1 : Y) * (((Φ x).2 : Y) * ((Φ x).1 : Y))⁻¹ = ((Φ x).2 : Y)⁻¹
    group
  rw [e1]
  exact C.inv_mem (Φ x).2.2

end Abstract

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_d1KBar (p : ℕ) (M H : Subgroup G) :
    ⁅d1KBar p M H, d1KBar p M H⁆ = d1KBar p M H := by
  refine le_antisymm (by simpa only [sup_idem] using
    Subgroup.commutator_le_sup (d1KBar p M H) (d1KBar p M H)) (iSup₂_le fun L hL => ?_)
  exact (Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hL.1.2.2.1)).symm.le.trans
    (Subgroup.commutator_mono (le_d1KBar hL.1 hL.2) (le_d1KBar hL.1 hL.2))

theorem eq_bot_of_normal_le_d1X0 (h31 : KFactThreeOne) (hKP : CFSG.Open.IsKProper G) {p : ℕ}
    {P : Sylow p G} {M H₁ R₁ : Subgroup G} (he : D1Escape p P M H₁ R₁) {B N : Subgroup G}
    (hB : IsAGLQ p M B) (hBN : B ≤ N) (hNtop : N ≠ ⊤) (hK : d1KBar p M N ≠ ⊥)
    {T : Subgroup (d1KBar p M N)} (hT : T.Normal)
    (hTX : T ≤ (d1X0 p M N).subgroupOf (d1KBar p M N)) : T = ⊥ := by
  set T' : Subgroup (N ⧸ primeComplementCore (G := N) p) := T.map (d1KBar p M N).subtype
  have hT'n : ∀ a ∈ d1KBar p M N, ∀ x ∈ T', a * x * a⁻¹ ∈ T' := by
    rintro a ha _ ⟨t, ht, rfl⟩
    exact ⟨⟨a, ha⟩ * t * ⟨a, ha⟩⁻¹, hT.conj_mem t ht ⟨a, ha⟩, rfl⟩
  have hLn : ∀ L : Subgroup (N ⧸ primeComplementCore (G := N) p), IsComponentOf L ⊤ →
      d1KBar p M N ≤ Subgroup.normalizer (L : Set (N ⧸ primeComplementCore (G := N) p)) := by
    intro L hL
    refine iSup₂_le fun L' hL' => ?_
    by_cases hLL : L' = L
    · rw [hLL]
      exact Subgroup.le_normalizer
    · exact (le_centralizer_of_component_ne hL'.1 hL hLL).trans
        (Subgroup.centralizer_le_normalizer _)
  have hcomm : ∀ t ∈ T', ∀ L : Subgroup (N ⧸ primeComplementCore (G := N) p),
      IsComponentOf L ⊤ → ¬ L ≤ d1X0 p M N → ∀ l ∈ L, t * l = l * t := by
    intro t ht L hL hLX l hl
    obtain ⟨hs, -, -⟩ := isSimpleGroup_catalog_of_component h31 hKP he hB hBN hNtop hL hLX
    have hLK : L ≤ d1KBar p M N := le_d1KBar hL hLX
    have htK : t ∈ d1KBar p M N := by
      obtain ⟨t₀, -, rfl⟩ := ht
      exact t₀.2
    set TL : Subgroup L := T'.subgroupOf L
    have hTLn : TL.Normal := ⟨fun x hx g => Subgroup.mem_subgroupOf.mpr
      (hT'n _ (hLK g.2) _ (Subgroup.mem_subgroupOf.mp hx))⟩
    have hTL : TL = ⊥ := by
      haveI := hs
      haveI := hTLn
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal TL with h | h
      · exact h
      · refine absurd (fun y hy => ?_) hLX
        have hyT : y ∈ T' := Subgroup.mem_subgroupOf.mp (h ▸ Subgroup.mem_top (⟨y, hy⟩ : L))
        obtain ⟨t₀, ht₀, rfl⟩ := hyT
        exact Subgroup.mem_subgroupOf.mp (hTX ht₀)
    have hcL : t * l * t⁻¹ * l⁻¹ ∈ L :=
      L.mul_mem (((Subgroup.mem_normalizer_iff.mp (hLn L hL htK)) l).mp hl) (L.inv_mem hl)
    have hcT : t * l * t⁻¹ * l⁻¹ ∈ T' := by
      rw [mul_assoc t, mul_assoc t]
      exact T'.mul_mem ht (hT'n l (hLK hl) _ (T'.inv_mem ht))
    have h1 : (⟨_, hcL⟩ : L) ∈ TL := Subgroup.mem_subgroupOf.mpr hcT
    rw [hTL, Subgroup.mem_bot] at h1
    have h2 : t * l * t⁻¹ * l⁻¹ = 1 := congrArg Subtype.val h1
    calc t * l = (t * l * t⁻¹ * l⁻¹) * l * t := by group
      _ = l * t := by rw [h2, one_mul]
  have hZ := center_d1KBar_eq_bot_of_escape h31 hKP he hB hBN hNtop hK
  rw [eq_bot_iff]
  intro t ht
  have hKC : d1KBar p M N ≤ Subgroup.centralizer
      ({(t : N ⧸ primeComplementCore (G := N) p)} : Set (N ⧸ primeComplementCore (G := N) p)) :=
    iSup₂_le fun L hL l hl => by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact hcomm t ⟨t, ht, rfl⟩ L hL.1 hL.2 l hl
  have htc : t ∈ Subgroup.center (d1KBar p M N) := Subgroup.mem_center_iff.mpr fun k => Subtype.ext
    (Subgroup.mem_centralizer_iff.mp (hKC k.2) _ rfl).symm
  rw [hZ] at htc
  exact htc

theorem nineSeventeen_involves (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hOut : KFactNineThreeOutPClosed) (hR2 : KFactNineThreeRankTwo) (hSch : KFactCatalogSchreier)
    (hS : Setting G) (hKP : CFSG.Open.IsKProper G) {p : ℕ} {P : Sylow p G}
    {M H₁ R₁ : Subgroup G} (he : D1Escape p P M H₁ R₁) {B H N : Subgroup G} (hB : IsAGLQ p M B)
    (hBH : B ≤ H) (hBN : B ≤ N) (hHtop : H ≠ ⊤) (hNtop : N ≠ ⊤) (hKH : d1KBar p M H ≠ ⊥)
    (hKN : d1KBar p M N ≠ ⊥) (hcov : AGLCovers p H N (d1KBar p M H)) :
    CFSG.QuasiDihedralFusion.Involves (d1KBar p M N) (d1KBar p M H) ∧
      d1Kappa p M H ≤ d1Kappa p M N ∧
      (d1Kappa p M H = d1Kappa p M N → ∀ x ∈ N, ∃ m ∈ N ⊓ M, ∃ y ∈ H ⊓ N, x = m * y) := by
  haveI := d1KBar_normal_of_escape he hB hBN hKN
  haveI : Group.IsPerfect (d1KBar p M H) := Subgroup.isPerfect_iff.mpr (commutator_d1KBar p M H)
  set πH := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set πN := QuotientGroup.mk' (primeComplementCore (G := N) p)
  set C := Subgroup.centralizer ((d1KBar p M N : Subgroup (N ⧸ primeComplementCore (G := N) p)) :
    Set (N ⧸ primeComplementCore (G := N) p))
  have hXM : ∀ n : N, πN n ∈ C → (n : G) ∈ M := fun n hn =>
    d1PlusCore_le_of_escape he hB hBN hKN ⟨n, hn, rfl⟩
  set W₀ : Subgroup G := (H ⊓ N) ⊓ ((d1KBar p M H).comap πH).map H.subtype with hW₀def
  have hW₀ : W₀ ≤ H ⊓ N := inf_le_left
  have hW₀H : W₀ ≤ H := hW₀.trans inf_le_left
  have hW₀N : W₀ ≤ N := hW₀.trans inf_le_right
  have hψ : ∀ w : W₀, πH (Subgroup.inclusion hW₀H w) ∈ d1KBar p M H := by
    rintro ⟨w, -, h, hh, rfl⟩
    exact hh
  set ψ : W₀ →* d1KBar p M H := (πH.comp (Subgroup.inclusion hW₀H)).codRestrict _ hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨k, hk⟩
    obtain ⟨h, hh, rfl⟩ := hcov hk
    exact ⟨⟨h, Subgroup.mem_subgroupOf.mp hh, h, hk, rfl⟩, rfl⟩
  set ρ : W₀ →* N ⧸ primeComplementCore (G := N) p := πN.comp (Subgroup.inclusion hW₀N)
  have hPψ := CFSG.LocalAnalysis.RankThreeTheoremC.map_perfectCore_comap ψ hψs ⊤
    Group.IsPerfect.commutator_eq_top
  rw [Subgroup.comap_top] at hPψ
  have hPρ := le_sup_centralizer_d1KBar_of_isPerfect h31 hSch hKP he hB hBN hNtop hKN
    (Z := (CFSG.LocalAnalysis.RankThreeTheoremC.perfectCore (⊤ : Subgroup W₀)).map ρ)
    (by rw [Subgroup.isPerfect_iff, ← Subgroup.map_commutator,
      CFSG.LocalAnalysis.RankThreeTheoremC.commutator_perfectCore])
  have hPX : ∀ x ∈ CFSG.LocalAnalysis.RankThreeTheoremC.perfectCore (⊤ : Subgroup W₀), ρ x ∈ C →
      ψ x ∈ (d1X0 p M H).subgroupOf (d1KBar p M H) := by
    intro x _ hx
    refine Subgroup.mem_subgroupOf.mpr ⟨Subgroup.inclusion hW₀H x, Subgroup.mem_subgroupOf.mpr
      ⟨hW₀H x.2, hXM (Subgroup.inclusion hW₀N x) hx⟩, rfl⟩
  obtain ⟨U, ⟨φ, hφ⟩, hU⟩ := exists_projection_surjective ψ ρ (d1KBar p M N)
    (center_d1KBar_eq_bot_of_escape h31 hKP he hB hBN hNtop hKN) _ hPψ hPρ _
    (fun T hT hTX => eq_bot_of_normal_le_d1X0 h31 hKP he hB hBH hHtop hKH hT hTX) hPX
  have hκU : d1Kappa p M H ≤ Nat.card U := Nat.card_le_card_of_surjective φ hφ
  have hUκ : Nat.card U ≤ d1Kappa p M N := Subgroup.card_le_card_group U
  refine ⟨⟨U, φ, hφ⟩, hκU.trans hUκ, fun hκ x hx => ?_⟩
  have hκU' : d1Kappa p M N ≤ Nat.card U := hκ ▸ hκU
  have hUtop : U = ⊤ := Subgroup.eq_top_of_card_eq U (le_antisymm hUκ hκU')
  obtain ⟨m, hm, k, hk, rfl⟩ :=
    (hyp93At_of_escape h31 h75 hOut hR2 hS hKP he hB hBN hNtop hKN).fac x hx
  obtain ⟨w, -, hw⟩ := hU ⟨πN k, hk⟩ (hUtop ▸ Subgroup.mem_top _)
  set w' : N := Subgroup.inclusion hW₀N w
  have hz : πN (k * w'⁻¹) ∈ C := by
    rw [map_mul, map_inv]
    exact hw
  refine ⟨(m : G) * ((k * w'⁻¹ : N) : G), ⟨N.mul_mem hm.1 (k * w'⁻¹).2,
    M.mul_mem hm.2 (hXM _ hz)⟩, (w : G), hW₀ w.2, ?_⟩
  simp [w', mul_assoc]

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
