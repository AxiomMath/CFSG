module

public import CFSG.LocalAnalysis.RankThreeUC.GN15Layer
public import CFSG.LocalAnalysis.RankThreeUC.GN15DQNormal

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Open
open scoped commutatorElement

section Dgen

private theorem exists_mul_of_mem_sup_of_le_centralizer'' {G : Type*} [Group G] {A K : Subgroup G}
    (hAK : A ≤ Subgroup.centralizer (K : Set G)) {x : G} (hx : x ∈ A ⊔ K) :
    ∃ a ∈ A, ∃ k ∈ K, x = a * k := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right A K
    (hAK.trans (Subgroup.centralizer_le_normalizer _))
  have hx' : x ∈ ((A ⊔ K : Subgroup G) : Set G) := hx
  rw [h] at hx'
  obtain ⟨a, ha, k, hk, rfl⟩ := hx'
  exact ⟨a, ha, k, hk, rfl⟩

private theorem mem_or_commutator_eq_bot_of_component {G : Type*} [Group G] [Finite G]
    {N L : Subgroup G} (hN : N.Normal) (hL : CFSG.IsComponent L) {u : G} (hu : u ∈ L)
    (h : ∀ y ∈ L, ⁅u, y⁆ ∈ N) : u ∈ N ∨ ∀ y ∈ L, ⁅u, y⁆ = 1 := by
  rcases CFSG.LocalCores.component_normal_subgroup hL hN with hLN | hLN
  · exact Or.inl (hLN hu)
  · right
    set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
    have hC : π u ∈ Subgroup.centralizer ((L.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      have h1 : π ⁅u, y⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (h y hy)
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    have hZ : (Subgroup.zpowers u) ≤ (Subgroup.centralizer
        ((L.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N))).comap π := by
      rw [Subgroup.zpowers_le]
      exact hC
    have hLX : ⁅Subgroup.zpowers u, L⁆ ≤ N := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      have hx' := Subgroup.mem_centralizer_iff.mp (hZ hx) (π y) ⟨y, hy, rfl⟩
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact hx'.symm
    have hdc : ⁅⁅L, Subgroup.zpowers u⁆, L⁆ = ⊥ := by
      refine le_bot_iff.mp ?_
      calc ⁅⁅L, Subgroup.zpowers u⁆, L⁆ = ⁅⁅Subgroup.zpowers u, L⁆, L⁆ := by
            rw [Subgroup.commutator_comm L (Subgroup.zpowers u)]
        _ ≤ ⁅N, L⁆ := Subgroup.commutator_mono hLX le_rfl
        _ = ⁅L, N⁆ := Subgroup.commutator_comm _ _
        _ = ⊥ := hLN
    have hP : Group.IsPerfect L := hL.1.1
    have := CFSG.LocalCores.perfect_double_commutator hP hdc
    intro y hy
    have hmem : ⁅u, y⁆ ∈ (⁅L, Subgroup.zpowers u⁆ : Subgroup G) := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers u) hy
    rw [this] at hmem
    exact Subgroup.mem_bot.mp hmem


private theorem comm_of_mem_sup_aux {G : Type*} [Group G] {A B : Subgroup G} {z : G}
    (hA : ∀ a ∈ A, z * a = a * z) (hB : ∀ b ∈ B, z * b = b * z) :
    ∀ g ∈ A ⊔ B, z * g = g * z := fun g hg => by
  have h : A ⊔ B ≤ Subgroup.centralizer ({z} : Set G) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.2 (hA a ha).symm)
      (fun b hb => Subgroup.mem_centralizer_singleton_iff.2 (hB b hb).symm)
  exact (Subgroup.mem_centralizer_singleton_iff.1 (h hg)).symm

theorem exists_mul_of_forall_commutator_mem {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    (hN : N.Normal) (F : Finset (Subgroup G)) (hF : ∀ L ∈ F, CFSG.Open.IsComponentOf L ⊤) :
    ∀ x ∈ (⨆ L ∈ F, L : Subgroup G), (∀ y ∈ (⨆ L ∈ F, L : Subgroup G), ⁅x, y⁆ ∈ N) →
      ∃ β ∈ N, ∃ ζ ∈ (⨆ L ∈ F, L : Subgroup G),
        (∀ y ∈ (⨆ L ∈ F, L : Subgroup G), ζ * y = y * ζ) ∧ x = β * ζ := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro x hx _
    have hbot : (⨆ L ∈ (∅ : Finset (Subgroup G)), L : Subgroup G) = ⊥ := by simp
    rw [hbot, Subgroup.mem_bot] at hx
    subst hx
    refine ⟨1, one_mem _, 1, one_mem _, fun y _ => by simp, by simp⟩
  | insert L₀ F hL₀ ih =>
    intro x hx hc
    rw [Finset.iSup_insert] at hx hc ⊢
    have hL₀c : CFSG.IsComponent L₀ :=
      (CFSG.isComponent_iff_open L₀).2 (hF L₀ (Finset.mem_insert_self _ _))
    have hFc : ∀ L ∈ F, CFSG.Open.IsComponentOf L ⊤ := fun L hL =>
      hF L (Finset.mem_insert_of_mem hL)
    set S : Subgroup G := ⨆ L ∈ F, L with hSdef
    have hLc : ∀ L ∈ F, L ≤ Subgroup.centralizer (L₀ : Set G) := by
      intro L hL
      have hLne : L₀ ≠ L := fun h => hL₀ (h ▸ hL)
      rcases CFSG.LocalCores.distinct_components_commute hL₀c
        ((CFSG.isComponent_iff_open L).2 (hFc L hL)) with h | h
      · exact absurd h hLne
      · rw [Subgroup.le_centralizer_iff]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    have hSc : S ≤ Subgroup.centralizer (L₀ : Set G) := iSup₂_le fun L hL => hLc L hL
    have hL₀S : L₀ ≤ Subgroup.centralizer (S : Set G) := Subgroup.le_centralizer_iff.1 hSc
    have hcomm : ∀ u ∈ L₀, ∀ s ∈ S, u * s = s * u := fun u hu s hs =>
      (Subgroup.mem_centralizer_iff.mp (hL₀S hu) s hs).symm
    obtain ⟨u, hu, s, hs, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer'' hL₀S hx
    have hcs : ∀ y ∈ S, ⁅s, y⁆ ∈ N := by
      intro y hy
      have h1 := hc y (Subgroup.mem_sup_right hy)
      have h2 : u * (s * y * s⁻¹) = (s * y * s⁻¹) * u :=
        hcomm u hu _ (S.mul_mem (S.mul_mem hs hy) (S.inv_mem hs))
      have : ⁅u * s, y⁆ = ⁅s, y⁆ := by
        have e1 : ⁅u * s, y⁆ = u * (s * y * s⁻¹) * u⁻¹ * y⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e1, h2]
        simp only [commutatorElement_def]; group
      rw [← this]
      exact h1
    have hcu : ∀ y ∈ L₀, ⁅u, y⁆ ∈ N := by
      intro y hy
      have h1 := hc y (Subgroup.mem_sup_left hy)
      have h2 : s * y = y * s := (hcomm y hy s hs).symm
      have : ⁅u * s, y⁆ = ⁅u, y⁆ := by
        have e1 : ⁅u * s, y⁆ = u * (s * y) * s⁻¹ * u⁻¹ * y⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e1, h2]
        simp only [commutatorElement_def]; group
      rw [← this]
      exact h1
    obtain ⟨β', hβ', ζ', hζ', hζc, rfl⟩ := ih hFc s hs hcs
    rcases mem_or_commutator_eq_bot_of_component hN hL₀c hu hcu with huN | hu1
    · refine ⟨u * β', N.mul_mem huN hβ', ζ', Subgroup.mem_sup_right hζ', ?_, by group⟩
      exact comm_of_mem_sup_aux (fun a ha => (hcomm a ha ζ' hζ').symm) hζc
    · have hu1' : ∀ y ∈ L₀, u * y = y * u := fun y hy =>
        (commutatorElement_eq_one_iff_mul_comm.1 (hu1 y hy))
      refine ⟨u * β' * u⁻¹, hN.conj_mem β' hβ' u, u * ζ',
        (L₀ ⊔ S).mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hζ'), ?_, by group⟩
      refine comm_of_mem_sup_aux (fun a ha => ?_) (fun b hb => ?_)
      · calc u * ζ' * a = u * (ζ' * a) := by group
          _ = u * (a * ζ') := by rw [(hcomm a ha ζ' hζ')]
          _ = (u * a) * ζ' := by group
          _ = (a * u) * ζ' := by rw [hu1' a ha]
          _ = a * (u * ζ') := by group
      · calc u * ζ' * b = u * (ζ' * b) := by group
          _ = u * (b * ζ') := by rw [hζc b hb]
          _ = (u * b) * ζ' := by group
          _ = (b * u) * ζ' := by rw [hcomm u hu b hb]
          _ = b * (u * ζ') := by group


end Dgen

section Diag

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

omit [Finite X] in
theorem gnC_le_gnHPre_cover : gnC T ≤ gnHPre T := fun z hz => by
  show toStar T z ∈ Subgroup.centralizer _
  rw [show toStar T z = 1 from (QuotientGroup.eq_one_iff _).2 hz]
  exact Subgroup.one_mem _

omit [Finite X] in
private theorem gnDStar_le_layer_cover :
    gnDStar T ≤ rankThreeLayer (⊤ : Subgroup (X ⧸ gnC T)) :=
  iSup₂_le fun _ hL => le_sSup hL.1

omit [Finite X] in
theorem gnDPre_le_gnLayerPre_cover : gnDPre T ≤ gnLayerPre T := fun _ hd =>
  Subgroup.mem_comap.2 (gnDStar_le_layer_cover (Subgroup.mem_comap.1 hd))

omit [Finite X] in
private theorem commutator_mem_gnC_of_mem_gnHPre {k e : X} (hk : k ∈ gnHPre T)
    (he : e ∈ gnDPre T) : k * e * k⁻¹ * e⁻¹ ∈ gnC T := by
  have hk' : toStar T k ∈ Subgroup.centralizer
      ((rankThreeLayer (⊤ : Subgroup (X ⧸ gnC T)) : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) := hk
  have he' : toStar T e ∈ rankThreeLayer (⊤ : Subgroup (X ⧸ gnC T)) :=
    gnDStar_le_layer_cover (Subgroup.mem_comap.1 he)
  have hc : toStar T e * toStar T k = toStar T k * toStar T e :=
    Subgroup.mem_centralizer_iff.mp hk' (toStar T e) he'
  refine (QuotientGroup.eq_one_iff _).1 ?_
  show toStar T (k * e * k⁻¹ * e⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  calc toStar T k * toStar T e * (toStar T k)⁻¹ * (toStar T e)⁻¹
      = (toStar T k * toStar T e) * (toStar T e * toStar T k)⁻¹ := by group
    _ = 1 := by rw [hc]; group

omit [Finite X] in
private theorem commutator_mem_of_mul_mem {A B : Subgroup X} (hA : A.Normal)
    (hB : B.Normal) (hD : (gnDPre T).Normal) (hCB : gnC T ≤ B) (hAD : A ⊓ gnDPre T ≤ B)
    {b k d : X} (hb : b ∈ B) (hk : k ∈ gnHPre T) (ha : b * (k * d) ∈ A)
    {d' : X} (hd' : d' ∈ gnDPre T) : d * d' * d⁻¹ * d'⁻¹ ∈ B := by
  set a : X := b * (k * d) with hadef
  have h1 : a * d' * a⁻¹ * d'⁻¹ ∈ B := by
    refine hAD ⟨?_, ?_⟩
    · have : a * d' * a⁻¹ * d'⁻¹ = a * (d' * a⁻¹ * d'⁻¹) := by group
      rw [this]
      exact A.mul_mem ha (hA.conj_mem _ (A.inv_mem ha) d')
    · exact (gnDPre T).mul_mem (hD.conj_mem d' hd' a) ((gnDPre T).inv_mem hd')
  set e : X := d * d' * d⁻¹ with hedef
  have heD : e ∈ gnDPre T :=
    hD.conj_mem d' hd' d
  have hc : k * e * k⁻¹ * e⁻¹ ∈ B := hCB (commutator_mem_gnC_of_mem_gnHPre hk heD)
  have h2 : a * d' * a⁻¹ * d'⁻¹ = b * ((k * e * k⁻¹ * e⁻¹) * (e * b⁻¹ * d'⁻¹)) := by
    simp only [hadef, hedef]
    group
  rw [h2] at h1
  have h3 : e * b⁻¹ * d'⁻¹ ∈ B := by
    have := B.mul_mem (B.inv_mem (B.mul_mem hb hc)) h1
    simpa [mul_assoc] using this
  have h4 : e * d'⁻¹ = (e * b⁻¹ * d'⁻¹) * (d' * b * d'⁻¹) := by group
  have h5 : e * d'⁻¹ ∈ B := by
    rw [h4]
    exact B.mul_mem h3 (hB.conj_mem b hb d')
  simpa [hedef, mul_assoc] using h5

theorem le_sup_gnHPre_of_le_sup_gnKMin_sup_gnDPre (hX : GNSetting X T) {A B : Subgroup X}
    (hA : A.Normal) (hB : B.Normal) (hCB : gnC T ≤ B) (hAD : A ⊓ gnDPre T ≤ B)
    (hAKD : A ≤ B ⊔ (gnKMin T ⊔ gnDPre T)) : A ≤ B ⊔ gnHPre T := by
  have := gnKMin_normal (T := T)
  have hD := gnDPre_normal hX
  have := hB
  intro a ha
  obtain ⟨b₀, hb₀, y, hy, hay⟩ := Subgroup.mem_sup_of_normal_left.mp (hAKD ha)
  obtain ⟨k, hk, d, hd, hyk⟩ := Subgroup.mem_sup_of_normal_left.mp hy
  have hkH : k ∈ gnHPre T := gnKMin_le_gnHPre hk
  have ha' : b₀ * (k * d) ∈ A := by rw [hyk, hay]; exact ha
  have hdD : d ∈ B ⊔ gnHPre T := by
    set S : Set (Subgroup (X ⧸ gnC T)) :=
      {L | IsComponentOf L ⊤ ∧ ⁅L, gnImg T (thompsonJ T)⁆ ≠ ⊥} with hS
    have hfin : S.Finite := Set.toFinite S
    have hDst : (⨆ L ∈ hfin.toFinset, L : Subgroup (X ⧸ gnC T)) = gnDStar T :=
      le_antisymm
        (iSup₂_le fun L hL => le_iSup₂_of_le L (hfin.mem_toFinset.1 hL) le_rfl)
        (iSup₂_le fun L hL => le_iSup₂_of_le L (hfin.mem_toFinset.2 hL) le_rfl)
    have hBn : (B.map (toStar T)).Normal := hB.map _ (QuotientGroup.mk'_surjective _)
    have hx : toStar T d ∈ (⨆ L ∈ hfin.toFinset, L : Subgroup (X ⧸ gnC T)) := by
      rw [hDst]
      exact Subgroup.mem_comap.1 hd
    have hcomm : ∀ y ∈ (⨆ L ∈ hfin.toFinset, L : Subgroup (X ⧸ gnC T)),
        ⁅toStar T d, y⁆ ∈ B.map (toStar T) := by
      intro y hy
      rw [hDst] at hy
      obtain ⟨d', rfl⟩ := QuotientGroup.mk_surjective y
      have hd'D : d' ∈ gnDPre T := hy
      refine ⟨d * d' * d⁻¹ * d'⁻¹, commutator_mem_of_mul_mem hA hB hD hCB hAD hb₀ hkH ha' hd'D,
        ?_⟩
      simp [commutatorElement_def]
    obtain ⟨β, hβ, ζ, hζ, hζc, hdβζ⟩ := exists_mul_of_forall_commutator_mem hBn hfin.toFinset
      (fun L hL => (hfin.mem_toFinset.1 hL).1) _ hx hcomm
    have hζE : ζ ∈ Subgroup.centralizer
        ((rankThreeLayer (⊤ : Subgroup (X ⧸ gnC T)) : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) := by
      have hle : rankThreeLayer (⊤ : Subgroup (X ⧸ gnC T)) ≤
          Subgroup.centralizer ({ζ} : Set (X ⧸ gnC T)) := by
        refine sSup_le fun L' hL' y hy => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        by_cases hL'S : L' ∈ S
        · have hLle : L' ≤ (⨆ L ∈ hfin.toFinset, L : Subgroup (X ⧸ gnC T)) :=
            le_iSup₂_of_le L' (hfin.mem_toFinset.2 hL'S) le_rfl
          exact (hζc y (hLle hy)).symm
        · have hcent : (⨆ L ∈ hfin.toFinset, L : Subgroup (X ⧸ gnC T)) ≤
              Subgroup.centralizer (L' : Set (X ⧸ gnC T)) := by
            refine iSup₂_le fun L hL => ?_
            have hLS := hfin.mem_toFinset.1 hL
            have hne : L ≠ L' := fun h => hL'S (h ▸ hLS)
            rcases CFSG.LocalCores.distinct_components_commute
              ((CFSG.isComponent_iff_open L).2 hLS.1) ((CFSG.isComponent_iff_open L').2 hL')
              with h | h
            · exact absurd h hne
            · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
          exact Subgroup.mem_centralizer_iff.mp (hcent hζ) y hy
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy))
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective ζ
    obtain ⟨b₁, hb₁, rfl⟩ := hβ
    have hzH : z ∈ gnHPre T := hζE
    have hc'' : (b₁ * z)⁻¹ * d ∈ gnC T := by
      refine QuotientGroup.eq.1 ?_
      rw [QuotientGroup.mk_mul]
      exact hdβζ.symm
    have hdeq : d = b₁ * (z * ((b₁ * z)⁻¹ * d)) := by group
    rw [hdeq]
    exact mul_mem (Subgroup.mem_sup_left hb₁) (Subgroup.mem_sup_right
      ((gnHPre T).mul_mem hzH (gnC_le_gnHPre_cover hc'')))
  have : a = b₀ * (k * d) := by rw [hyk, hay]
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left hb₀) (mul_mem (Subgroup.mem_sup_right hkH) hdD)

end Diag

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
