module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RHQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75E8
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

theorem exists_mul_of_mem_sup_comm' {G : Type} [Group G] {A B : Subgroup G}
    (hAB : B ≤ centralizer (A : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hn : A ≤ normalizer (B : Set G) := fun a ha =>
    centralizer_le_normalizer _ ((Subgroup.le_centralizer_iff.mp hAB) ha)
  have h := Subgroup.coe_mul_of_left_le_normalizer_right A B hn
  have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
  rw [h] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem harada_contradiction (hH : Harada75E8) {G : Type} [Group G] [Finite G] {z σ ξ : G}
    (hz : z * z = 1) (hσ : σ * σ = 1) (hzσ : z * σ = σ * z)
    (hnc : ¬ ∃ g : G, g * z * g⁻¹ = σ)
    {D : Subgroup G} (hD2 : IsPGroup 2 D) (hDz : D ≤ centralizer ({z} : Set G))
    (hDσ : D ≤ centralizer ({σ} : Set G))
    (hDmax : ∀ R : Subgroup G, IsPGroup 2 R →
      R ≤ centralizer ({z} : Set G) ⊓ centralizer ({σ} : Set G) → D ≤ R → R ≤ D)
    {A₀ : Subgroup G} (hA₀D : A₀ ≤ D) (hA₀ : IsElemAbelian 2 A₀) (hA₀8 : Nat.card A₀ = 8)
    (hzA : z ∈ A₀) (huA : z * σ ∉ A₀)
    (hcent : ∀ s ∈ D, (∀ a ∈ A₀, s * a * s⁻¹ * a⁻¹ ∈ zpowers (z * σ)) →
      s ∈ A₀ ⊔ zpowers (z * σ))
    (hξ : ∃ g : G, g * (z * σ) * g⁻¹ = ξ)
    {R : Subgroup G} (hR2 : IsPGroup 2 R) (hRξ : R ≤ centralizer ({ξ} : Set G)) (hξR : ξ ∈ R)
    (h5 : ∀ X : Finset G, (↑X : Set G) ⊆ ↑R → X.card ≤ 4 →
      closure (X : Set G) ⊔ zpowers ξ ≠ R) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := hξ
  set u : G := z * σ with hu_def
  have hzσ' : σ * z = z * σ := hzσ.symm
  have hu2 : u * u = 1 := by
    calc u * u = z * (σ * z) * σ := by rw [hu_def]; group
      _ = z * (z * σ) * σ := by rw [hzσ']
      _ = (z * z) * (σ * σ) := by group
      _ = 1 := by rw [hz, hσ, one_mul]
  have hu1 : u ≠ 1 := by
    intro h
    apply hnc
    refine ⟨1, ?_⟩
    have h1 : σ = z⁻¹ := by
      have := eq_inv_of_mul_eq_one_right h
      exact this
    rw [h1, inv_eq_of_mul_eq_one_right hz]
    group
  have hzu : z * u = σ := by
    calc z * u = (z * z) * σ := by rw [hu_def]; group
      _ = σ := by rw [hz, one_mul]
  have huz : u * z = σ := by
    calc u * z = z * σ * z := rfl
      _ = z * (σ * z) := by group
      _ = z * (z * σ) := by rw [hzσ']
      _ = (z * z) * σ := by group
      _ = σ := by rw [hz, one_mul]
  have hcomm_u : ∀ d ∈ D, d * u = u * d := by
    intro d hd
    have h1 : d * z = z * d := mem_centralizer_singleton_iff.1 (hDz hd)
    have h2 : d * σ = σ * d := mem_centralizer_singleton_iff.1 (hDσ hd)
    calc d * u = d * z * σ := by rw [hu_def]; group
      _ = z * d * σ := by rw [h1]
      _ = z * (d * σ) := by group
      _ = z * (σ * d) := by rw [h2]
      _ = u * d := by rw [hu_def]; group
  have hDV : D ≤ centralizer ({u} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (hcomm_u d hd)
  have hA₀V : A₀ ≤ centralizer ({u} : Set G) := fun a ha => hDV (hA₀D ha)
  have hDV2 : IsPGroup 2 (D.subgroupOf (centralizer ({u} : Set G))) := hD2.comap_subtype
  let Dbar : Subgroup (Vbar u) := (D.subgroupOf (centralizer ({u} : Set G))).map (mkV u)
  have hDbar2 : IsPGroup 2 Dbar := hDV2.map _
  obtain ⟨S, hDS⟩ := hDbar2.exists_le_sylow
  let ψ : ↥A₀ →* Vbar u := (mkV u).comp (Subgroup.inclusion hA₀V)
  have hψker : ∀ w : ↥A₀, ψ w = 1 → w = 1 := by
    intro w hw
    rcases (mkV_eq_one_iff hu2 _).1 hw with h | h
    · exact Subtype.ext (by simpa using h)
    · exfalso
      apply huA
      have : (w : G) = u := by simpa using h
      rw [← this]
      exact w.2
  have hψinj : Function.Injective ψ := (injective_iff_map_eq_one ψ).2 hψker
  have hcardbar : Nat.card ψ.range = 8 := by
    rw [← hA₀8]
    exact (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  have hbarS : ψ.range ≤ (S : Subgroup (Vbar u)) := by
    rintro _ ⟨a, rfl⟩
    apply hDS
    exact ⟨Subgroup.inclusion hA₀V a, mem_subgroupOf.2 (hA₀D a.2), rfl⟩
  have hcommR : ∀ x y : Vbar u, x ∈ ψ.range → y ∈ ψ.range → x * y = y * x := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact hA₀.1.is_comm.comm a b
  have hsqR : ∀ x ∈ ψ.range, x ^ 2 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (by simpa using hA₀.2 a a.2)
    rw [this, map_one]
  have hcentS : Subgroup.centralizer ((ψ.range.subgroupOf (S : Subgroup (Vbar u)) :
      Subgroup ↥(S : Subgroup (Vbar u))) : Set ↥(S : Subgroup (Vbar u))) ≤
      ψ.range.subgroupOf (S : Subgroup (Vbar u)) := by
    intro t ht
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (t : Vbar u)
    have hv' : mkV u v = (t : Vbar u) := hv
    have hvA : ∀ a ∈ A₀, (v : G) * a * (v : G)⁻¹ * a⁻¹ ∈ zpowers u := by
      intro a ha
      let aV : ↥(centralizer ({u} : Set G)) := ⟨a, hA₀V ha⟩
      let a' : ↥(S : Subgroup (Vbar u)) := ⟨ψ ⟨a, ha⟩, hbarS ⟨_, rfl⟩⟩
      have ha'mem : a' ∈ ψ.range.subgroupOf (S : Subgroup (Vbar u)) := ⟨⟨a, ha⟩, rfl⟩
      have h1 := mem_centralizer_iff.1 ht a' ha'mem
      have h2 : ψ ⟨a, ha⟩ * (t : Vbar u) = (t : Vbar u) * ψ ⟨a, ha⟩ := congrArg Subtype.val h1
      have h3 : mkV u (v * aV * v⁻¹ * aV⁻¹) = 1 := by
        have e1 : ψ ⟨a, ha⟩ = mkV u aV := rfl
        rw [e1, ← hv'] at h2
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        have h4 : mkV u v * mkV u aV = mkV u aV * mkV u v := h2.symm
        calc mkV u v * mkV u aV * (mkV u v)⁻¹ * (mkV u aV)⁻¹
            = (mkV u aV * mkV u v) * (mkV u v)⁻¹ * (mkV u aV)⁻¹ := by rw [h4]
          _ = 1 := by group
      rcases (mkV_eq_one_iff hu2 _).1 h3 with h | h
      · have : (v : G) * a * (v : G)⁻¹ * a⁻¹ = 1 := by simpa [aV] using h
        rw [this]; exact one_mem _
      · have : (v : G) * a * (v : G)⁻¹ * a⁻¹ = u := by simpa [aV] using h
        rw [this]; exact mem_zpowers u
    have hvz : (v : G) * z * (v : G)⁻¹ = z := by
      have h1 := hvA z hzA
      have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
      rcases mem_zpowers_sq_eq_one hu2 h1 with h | h
      · rw [hzi] at h
        calc (v : G) * z * (v : G)⁻¹ = ((v : G) * z * (v : G)⁻¹ * z) * z⁻¹ := by group
          _ = z := by rw [h, hzi]; group
      · exfalso
        apply hnc
        refine ⟨(v : G), ?_⟩
        rw [hzi] at h
        calc (v : G) * z * (v : G)⁻¹ = ((v : G) * z * (v : G)⁻¹ * z) * z⁻¹ := by group
          _ = σ := by rw [h, hzi, huz]
    have hvu : (v : G) * u * (v : G)⁻¹ = u := by
      have := mem_centralizer_singleton_iff.1 v.2
      calc (v : G) * u * (v : G)⁻¹ = (u * (v : G)) * (v : G)⁻¹ := by rw [this]
        _ = u := by group
    have hvσ : (v : G) * σ * (v : G)⁻¹ = σ := by
      calc (v : G) * σ * (v : G)⁻¹ = (v : G) * (z * u) * (v : G)⁻¹ := by rw [hzu]
        _ = ((v : G) * z * (v : G)⁻¹) * ((v : G) * u * (v : G)⁻¹) := by group
        _ = σ := by rw [hvz, hvu, hzu]
    have hHv2 : IsPGroup 2 ((S : Subgroup (Vbar u)).comap (mkV u)) :=
      isPGroup_comap_mkV hu2 hu1 S.isPGroup'
    let Pt : Subgroup ↥(centralizer ({u} : Set G)) :=
      (S : Subgroup (Vbar u)).comap (mkV u) ⊓
        (centralizer ({z} : Set G) ⊓ centralizer ({σ} : Set G)).subgroupOf (centralizer ({u} : Set G))
    have hPt2 : IsPGroup 2 Pt := hHv2.to_le inf_le_left
    have hPtG2 : IsPGroup 2 (Pt.map (centralizer ({u} : Set G)).subtype) := hPt2.map _
    have hPtGY : Pt.map (centralizer ({u} : Set G)).subtype ≤
        centralizer ({z} : Set G) ⊓ centralizer ({σ} : Set G) := by
      rintro _ ⟨p, hp, rfl⟩
      exact mem_subgroupOf.1 hp.2
    have hDPt : D ≤ Pt.map (centralizer ({u} : Set G)).subtype := by
      intro d hd
      refine ⟨⟨d, hDV hd⟩, ⟨?_, ?_⟩, rfl⟩
      · exact hDS ⟨⟨d, hDV hd⟩, mem_subgroupOf.2 hd, rfl⟩
      · exact mem_subgroupOf.2 ⟨hDz hd, hDσ hd⟩
    have hPtD := hDmax _ hPtG2 hPtGY hDPt
    have hvD : (v : G) ∈ D := by
      apply hPtD
      refine ⟨v, ⟨?_, ?_⟩, rfl⟩
      · show mkV u v ∈ (S : Subgroup (Vbar u))
        rw [hv']; exact t.2
      · exact mem_subgroupOf.2 ⟨mem_centralizer_singleton_iff.2 (by
          calc (v : G) * z = z * (v : G) := by
                calc (v : G) * z = ((v : G) * z * (v : G)⁻¹) * (v : G) := by group
                  _ = z * (v : G) := by rw [hvz]),
          mem_centralizer_singleton_iff.2 (by
            calc (v : G) * σ = ((v : G) * σ * (v : G)⁻¹) * (v : G) := by group
              _ = σ * (v : G) := by rw [hvσ])⟩
    have hvsup : (v : G) ∈ A₀ ⊔ zpowers u := hcent _ hvD hvA
    have hAu : zpowers u ≤ centralizer (A₀ : Set G) := by
      rw [zpowers_le]
      exact mem_centralizer_iff.2 fun a ha => (hcomm_u a (hA₀D ha))
    obtain ⟨a₀, ha₀, b, hb, hvab⟩ := exists_mul_of_mem_sup_comm' hAu hvsup
    have hw : mkV u ((⟨a₀, hA₀V ha₀⟩ : ↥(centralizer ({u} : Set G)))⁻¹ * v) = 1 := by
      rw [mkV_eq_one_iff hu2]
      have hval : ((((⟨a₀, hA₀V ha₀⟩ : ↥(centralizer ({u} : Set G)))⁻¹ * v : _) : G)) = b := by
        simp [hvab]
      rw [hval]
      rcases mem_zpowers_sq_eq_one hu2 hb with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hteq : (t : Vbar u) = ψ ⟨a₀, ha₀⟩ := by
      rw [← hv']
      have hsplit : v = (⟨a₀, hA₀V ha₀⟩ : ↥(centralizer ({u} : Set G))) *
          ((⟨a₀, hA₀V ha₀⟩ : ↥(centralizer ({u} : Set G)))⁻¹ * v) := by group
      calc mkV u v = mkV u ((⟨a₀, hA₀V ha₀⟩ : ↥(centralizer ({u} : Set G))) *
            ((⟨a₀, hA₀V ha₀⟩ : ↥(centralizer ({u} : Set G)))⁻¹ * v)) := by rw [← hsplit]
        _ = mkV u ⟨a₀, hA₀V ha₀⟩ * 1 := by rw [map_mul, hw]
        _ = ψ ⟨a₀, ha₀⟩ := by rw [mul_one]; rfl
    exact ⟨⟨a₀, ha₀⟩, hteq.symm⟩
  have hcardA : Nat.card ↥(ψ.range.subgroupOf (S : Subgroup (Vbar u))) = 8 := by
    rw [← hcardbar]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hbarS).toEquiv
  have hHS := hH ↥(S : Subgroup (Vbar u)) S.isPGroup' (ψ.range.subgroupOf (S : Subgroup (Vbar u)))
    ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (hcommR _ _ a.2 b.2))⟩⟩,
      fun x hx => Subtype.ext (hsqR _ hx)⟩ hcardA hcentS
  subst hg
  have hconjV : ∀ r : ↥R, g⁻¹ * (r : G) * g ∈ centralizer ({u} : Set G) := by
    intro r
    rw [mem_centralizer_singleton_iff]
    have h1 : (r : G) * (g * u * g⁻¹) = (g * u * g⁻¹) * (r : G) :=
      mem_centralizer_singleton_iff.1 (hRξ r.2)
    calc g⁻¹ * (r : G) * g * u = g⁻¹ * ((r : G) * (g * u * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * u * g⁻¹) * (r : G)) * g := by rw [h1]
      _ = u * (g⁻¹ * (r : G) * g) := by group
  let ψ' : ↥R →* ↥(centralizer ({u} : Set G)) :=
    { toFun := fun r => ⟨g⁻¹ * (r : G) * g, hconjV r⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp; group) }
  let Φ : ↥R →* Vbar u := (mkV u).comp ψ'
  have hΦker : ∀ r : ↥R, Φ r = 1 → (r : G) = 1 ∨ (r : G) = g * u * g⁻¹ := by
    intro r hr
    rcases (mkV_eq_one_iff hu2 (ψ' r)).1 hr with h | h
    · left
      have h' : g⁻¹ * (r : G) * g = 1 := h
      calc (r : G) = g * (g⁻¹ * (r : G) * g) * g⁻¹ := by group
        _ = 1 := by rw [h']; group
    · right
      have h' : g⁻¹ * (r : G) * g = u := h
      calc (r : G) = g * (g⁻¹ * (r : G) * g) * g⁻¹ := by group
        _ = g * u * g⁻¹ := by rw [h']
  have hΦ2 : IsPGroup 2 Φ.range := hR2.of_surjective Φ.rangeRestrict Φ.rangeRestrict_surjective
  obtain ⟨x, hx⟩ := exists_conj_le_sylow S hΦ2
  let Ψ : ↥R →* ↥(S : Subgroup (Vbar u)) :=
    { toFun := fun r => ⟨x⁻¹ * Φ r * x, hx _ ⟨r, rfl⟩⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp; group) }
  obtain ⟨X, hXcard, hXcl⟩ := hHS Ψ.range
  have hXmem : ∀ y ∈ X, ∃ r : ↥R, Ψ r = y := fun y hy => by
    have : y ∈ Subgroup.closure (X : Set ↥(S : Subgroup (Vbar u))) := subset_closure hy
    rw [hXcl] at this
    exact this
  choose! f hf using hXmem
  let X' : Finset G := X.image (fun y => ((f y : ↥R) : G))
  have hX'R : (↑X' : Set G) ⊆ ↑R := by
    intro w hw
    simp only [X', Finset.coe_image, Set.mem_image] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    exact (f y).2
  have hX'card : X'.card ≤ 4 := Finset.card_image_le.trans hXcard
  apply h5 X' hX'R hX'card
  apply le_antisymm
  · exact sup_le ((Subgroup.closure_le R).2 hX'R) (zpowers_le.2 hξR)
  · intro r hr
    let K : Subgroup ↥R := (Subgroup.closure (X' : Set G)).subgroupOf R
    have hle : Ψ.range ≤ K.map Ψ := by
      rw [← hXcl, Subgroup.closure_le]
      intro y hy
      refine ⟨f y, ?_, hf y hy⟩
      show ((f y : ↥R) : G) ∈ Subgroup.closure (X' : Set G)
      exact subset_closure (Finset.mem_image.2 ⟨y, hy, rfl⟩)
    obtain ⟨k, hk, hkr⟩ := hle ⟨⟨r, hr⟩, rfl⟩
    have hkernel : Ψ (k⁻¹ * ⟨r, hr⟩) = 1 := by
      rw [map_mul, map_inv, hkr, inv_mul_cancel]
    have hΦ1 : Φ (k⁻¹ * ⟨r, hr⟩) = 1 := by
      have h1 : x⁻¹ * Φ (k⁻¹ * ⟨r, hr⟩) * x = 1 := congrArg Subtype.val hkernel
      calc Φ (k⁻¹ * ⟨r, hr⟩) = x * (x⁻¹ * Φ (k⁻¹ * ⟨r, hr⟩) * x) * x⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have hkG : (k : G) ∈ Subgroup.closure (X' : Set G) := hk
    have hsplit : r = (k : G) * ((k⁻¹ * ⟨r, hr⟩ : ↥R) : G) := by
      simp
    rw [hsplit]
    refine mul_mem (mem_sup_left hkG) (mem_sup_right ?_)
    rcases hΦker _ hΦ1 with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact mem_zpowers _

end CFSG.EvenSporadicStandard.Fin76b
