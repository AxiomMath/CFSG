module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.Core
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.CocycleGen
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.ModuleStepGen
public import CFSG.Quasithin.Background.B2FactorizationBaumannAux
public import CFSG.CGT.PushingUpLit.BHS.OffenderInternal
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Star
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.Decomp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockBridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Quasithin CFSG.Quasithin.A4 CFSG.Open
  CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s_four_false_of_centralizes {S L : Subgroup G}
    (hA : Asc81bHyp (L ⊔ S) S) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    {r d : ℕ} (hr : r = 3 ∨ 5 ≤ r) (e : Fin d ≃ OmegaE r 4)
    (π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart d)) (θ : ↥(L ⊔ S) →* Perm (Fin d))
    (hker : π.ker =
      (⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅blockV S L, L⁆)
    (hAlt : ∀ σ ∈ alternatingGroup (Fin d),
      ∃ l : ↥L, θ ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ = σ)
    (hequiv : SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ)
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    (hW : ((thompsonJ S).subgroupOf (L ⊔ S)).map (e.permCongrHom.toMonoidHom.comp θ) = Wr r 4)
    (hZC : ∀ z ∈ omegaOneCenterOf (thompsonJ S), ∀ v ∈ blockV S L, z * v = v * z)
    (hZL : ∀ z ∈ omegaOneCenterOf (thompsonJ S), ∀ l ∈ L, ⁅l, z⁆ ∈ blockV S L)
    (hXL : ∀ z ∈ omegaOneCenterOf (thompsonJ S), ∀ k : ↥(L ⊔ S), θ k = 1 → ∀ l ∈ L,
      l * ⁅(k : G), z⁆ = ⁅(k : G), z⁆ * l)
    (hne : ⁅omegaOneCenterOf (thompsonJ S), S⁆ ≠ ⊥) : False := by
  classical
  have hSM : S ≤ L ⊔ S := le_sup_right
  have hLM : L ≤ L ⊔ S := le_sup_left
  let θ' : ↥(L ⊔ S) →* Perm (OmegaE r 4) := e.permCongrHom.toMonoidHom.comp θ
  have hθ'def : ∀ m, θ' m = e.permCongr (θ m) := fun m => rfl
  have hθ'e : ∀ m x, θ' m (e x) = e (θ m x) := fun m x => by
    rw [hθ'def]; simp [Equiv.permCongr_apply]
  have hθ'inj : ∀ m, θ' m = 1 → θ m = 1 := fun m h => by
    apply e.permCongrHom.injective
    rw [map_one]; exact h
  have hker' : ∀ m : ↥(L ⊔ S), θ' m = 1 → (m : G) ∈ S := fun m h => hθS m (hθ'inj m h)
  have hsign : ∀ σ : Perm (Fin d), sign (e.permCongr σ) = sign σ := fun σ =>
    Equiv.Perm.sign_permCongr e σ
  have hAltL : ∀ x ∈ alternatingGroup (OmegaE r 4), ∃ l : ↥L,
      θ' ⟨(l : G), hLM l.2⟩ = x := by
    intro x hx
    have hx' : e.permCongr.symm x ∈ alternatingGroup (Fin d) := by
      rw [mem_alternatingGroup] at hx ⊢
      rw [← hx]
      have := Equiv.Perm.sign_permCongr e (e.permCongr.symm x)
      rw [← this]; simp
    obtain ⟨l, hl⟩ := hAlt _ hx'
    exact ⟨l, by rw [hθ'def, hl]; exact Equiv.apply_symm_apply _ _⟩
  have hAlt' : ∀ x ∈ alternatingGroup (OmegaE r 4), ∃ m : ↥(L ⊔ S), θ' m = x := fun x hx => by
    obtain ⟨l, hl⟩ := hAltL x hx
    exact ⟨_, hl⟩
  have hdecomp := exists_decomp hA hSM hr θ' hker' hAlt' hW
  have hVel : IsElemAbelian 2 (blockV S L) :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isElemAbelian_blockV S L
  have hVc : ∀ a ∈ blockV S L, ∀ b ∈ blockV S L, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hV2 : ∀ a ∈ blockV S L, a ^ 2 = 1 := hVel.2
  have hMV : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.sup_le_normalizer_blockV S L
  have hVn : ∀ m ∈ L ⊔ S, ∀ v ∈ blockV S L, m * v * m⁻¹ ∈ blockV S L := fun m hm v hv =>
    (Subgroup.mem_normalizer_iff.1 (hMV hm) v).1 hv
  have hML : L ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (fun x hx => Subgroup.le_normalizer hx) hSL
  have hXn : ∀ m ∈ L ⊔ S, ∀ x ∈ ⁅blockV S L, L⁆, m * x * m⁻¹ ∈ ⁅blockV S L, L⁆ :=
    fun m hm x hx => conj_mem_commutator' (hMV hm) (hML hm) hx
  obtain ⟨c, hcalt, hc3, ⟨T0, hT0, hT0inl, hcfix⟩, hcN⟩ :=
    exists_threeCycle_not_mem_normalizer_Wr (r := r) (s := 4) (by omega)
  have hcinr : ∀ j : Fin 4, c (Sum.inr j) = Sum.inr j := fun j =>
    hcfix _ (fun hx => by obtain ⟨p, hp⟩ := hT0inl _ hx; exact Sum.inr_ne_inl hp)
  obtain ⟨l, hl⟩ := hAltL c hcalt
  obtain ⟨g, hgL, hgθ, m, hm, hgm⟩ : ∃ g : G, ∃ hgL : g ∈ L,
      θ' ⟨g, hLM hgL⟩ = c ∧ ∃ m : ℕ, Odd m ∧ g ^ m = 1 := by
    have hn : orderOf (l : G) ≠ 0 := (orderOf_pos _).ne'
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hn
    have hgL : (l : G) ^ 4 ^ k ∈ L := L.pow_mem l.2 _
    refine ⟨(l : G) ^ 4 ^ k, hgL, ?_, m, hm, ?_⟩
    · have h4 : 4 ^ k % 3 = 1 := by
        rw [Nat.pow_mod]; simp
      have : (⟨(l : G) ^ 4 ^ k, hLM hgL⟩ : ↥(L ⊔ S)) = (⟨(l : G), hLM l.2⟩ : ↥(L ⊔ S)) ^ 4 ^ k :=
        Subtype.ext (by simp)
      rw [this, map_pow, hl, ← Nat.div_add_mod (4 ^ k) 3, pow_add, pow_mul, hc3, one_pow, one_mul,
        h4, pow_one]
    · rw [← pow_mul]
      apply orderOf_dvd_iff_pow_eq_one.1
      rw [hkm]
      exact mul_dvd_mul_right ⟨2 ^ k, by rw [← mul_pow]; norm_num⟩ m
  have hgM : g ∈ L ⊔ S := hLM hgL
  let T : Finset (Fin d) := T0.image e.symm
  let Γ : Finset (Fin d) := (Finset.univ : Finset (Fin 4)).image fun j => e.symm (Sum.inr j)
  have hTc : T.card ≤ 3 := Finset.card_image_le.trans hT0
  have hΓc : Γ.card ≤ 4 := Finset.card_image_le.trans (by simp)
  have hTΓ : Disjoint T Γ := by
    rw [Finset.disjoint_left]
    intro x hxT hxΓ
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hxT
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hxΓ
    obtain ⟨p, hp⟩ := hT0inl t ht
    have : t = Sum.inr j := e.symm.injective hj.symm
    rw [hp] at this
    exact Sum.inl_ne_inr this
  have hd : 7 < d := by
    have h1 : d = Fintype.card (OmegaE r 4) := by
      rw [← Fintype.card_congr e]; simp
    simp only [OmegaE, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at h1
    omega
  have hg3 : g ^ 3 = 1 := by
    have h1 : θ' ⟨g ^ 3, hLM (L.pow_mem hgL 3)⟩ = 1 := by
      have : (⟨g ^ 3, hLM (L.pow_mem hgL 3)⟩ : ↥(L ⊔ S)) = (⟨g, hgM⟩ : ↥(L ⊔ S)) ^ 3 :=
        Subtype.ext (by simp)
      rw [this, map_pow, hgθ, hc3]
    have hS3 : g ^ 3 ∈ S := hker' _ h1
    obtain ⟨n, hn⟩ := hA.twoRadical.isPGroup ⟨g ^ 3, hS3⟩
    have hn' : (g ^ 3) ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have hm' : (g ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hgm, one_pow]
    have hcop : Nat.Coprime (2 ^ n) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hm)
    have := pow_gcd_eq_one.2 ⟨hn', hm'⟩
    simpa [Nat.Coprime.gcd_eq_one hcop] using this
  let Z₀ : Subgroup G := omegaOneCenterOf (thompsonJ S)
  have hZS : Z₀ ≤ S := (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _).trans
    (thompsonJ_le_self S)
  have hZchar : (Z₀.subgroupOf S).Characteristic :=
    CFSG.Quasithin.C1GN.characteristic_subgroupOf_trans (thompsonJ_le_self S)
      (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _)
      (CFSG.QuasithinUnique.Setup.characteristic_thompsonJ S)
      (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf (thompsonJ S))
  have hZnorm : ∀ s ∈ S, ∀ z ∈ Z₀, s * z * s⁻¹ ∈ Z₀ := by
    intro s hs z hz
    have hN : (Z₀.subgroupOf S).Normal := inferInstance
    have := hN.conj_mem ⟨z, hZS hz⟩ (Subgroup.mem_subgroupOf.2 hz) ⟨s, hs⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hYel : IsElemAbelian 2 (Z₀ ⊔ blockV S L) :=
    CFSG.CGT.PushingUpLit.BHS.isElemAbelian_sup' (B2F.isElemAbelian_omegaOneCenterOf _) hVel
      (fun z hz v hv => hZC z hz v hv)
  have hYc : ∀ a ∈ Z₀ ⊔ blockV S L, ∀ b ∈ Z₀ ⊔ blockV S L, a * b = b * a :=
    fun a ha b hb => CFSG.CGT.PushingUpLit.BHS.isElemAbelian_comm' hYel ha hb
  have hVY : blockV S L ≤ Z₀ ⊔ blockV S L := le_sup_right
  have hgZV : ∀ y ∈ Z₀ ⊔ blockV S L, ⁅g, y⁆ ∈ blockV S L :=
    commutator_mem_sup hVc (fun z hz v hv => hZC z hz v hv) (fun z hz => hZL z hz g hgL)
      (fun v hv => hVn g hgM v hv)
  have hgY : ∀ y ∈ Z₀ ⊔ blockV S L, g * y * g⁻¹ ∈ Z₀ ⊔ blockV S L := by
    intro y hy
    have e : g * y * g⁻¹ = ⁅g, y⁆ * y := by rw [commutatorElement_def]; group
    rw [e]; exact (Z₀ ⊔ blockV S L).mul_mem (hVY (hgZV y hy)) hy
  have hgX : ∀ v ∈ blockV S L, ⁅g, v⁆ ∈ ⁅blockV S L, L⁆ := by
    intro v hv
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hv hgL)
  have hkey : ∀ δ : ↥(L ⊔ S), (δ : G) ∈ S → (∀ p, θ' δ (Sum.inl p) = Sum.inl p) →
      θ' δ ∈ alternatingGroup (OmegaE r 4) → ∀ z ∈ Z₀,
      g * ⁅(δ : G), z⁆ * g⁻¹ = ⁅(δ : G), z⁆ := by
    intro δ hδS hδfix hδalt z hz
    have hδM : (δ : G) ∈ L ⊔ S := δ.2
    have hδalt' : θ δ ∈ alternatingGroup (Fin d) := by
      rw [mem_alternatingGroup] at hδalt ⊢
      rw [← hsign (θ δ)]
      exact hδalt
    have hcomm' : θ ⟨g, hgM⟩ * θ δ = θ δ * θ ⟨g, hgM⟩ := by
      apply e.permCongrHom.injective
      have h := perm_commute_of_fix c (θ' δ) hcinr hδfix
      rw [← hgθ] at h
      rw [map_mul, map_mul]
      exact h
    let kM : ↥(L ⊔ S) := (δ * ⟨g, hgM⟩)⁻¹ * (⟨g, hgM⟩ * δ)
    have hkθ : θ kM = 1 := by
      show θ ((δ * ⟨g, hgM⟩)⁻¹ * (⟨g, hgM⟩ * δ)) = 1
      rw [map_mul, map_inv, map_mul, map_mul, hcomm']
      exact inv_mul_cancel _
    have hkdef : (kM : G) = ((δ : G) * g)⁻¹ * (g * (δ : G)) := rfl
    have hkS : (kM : G) ∈ S := hθS kM hkθ
    have hcT : ∀ x ∉ T, θ ⟨g, hgM⟩ x = x := by
      intro x hx
      have hx' : e x ∉ T0 := fun h => hx (Finset.mem_image.2 ⟨e x, h, by simp⟩)
      have h2 := hcfix _ hx'
      rw [← hgθ, hθ'e] at h2
      exact e.injective h2
    have hfΓ : ∀ x ∉ Γ, θ δ x = x := by
      intro x hx
      rcases hx' : e x with p | j
      · have h2 := hδfix p
        rw [← hx', hθ'e] at h2
        exact e.injective (by rw [h2, hx'])
      · exfalso
        exact hx (Finset.mem_image.2 ⟨j, Finset.mem_univ _, by rw [← hx']; simp⟩)
    have hzY : z ∈ Z₀ ⊔ blockV S L := Subgroup.mem_sup_left hz
    have hu : ⁅g, z⁆ ∈ blockV S L := hZL z hz g hgL
    have hw0 : ⁅(δ : G), z⁆ ∈ Z₀ := by
      rw [commutatorElement_def]
      exact Z₀.mul_mem (hZnorm δ hδS z hz) (Z₀.inv_mem hz)
    have hwY : ⁅(δ : G), z⁆ ∈ Z₀ ⊔ blockV S L := Subgroup.mem_sup_left hw0
    have hκV : ⁅g, ⁅(δ : G), z⁆⁆ ∈ blockV S L := hZL _ hw0 g hgL
    have hrel := commutator_g_commutator_eq hYc (g := g) (δ := (δ : G)) (z := z)
      (hVY hu) hwY
    set u : G := ⁅g, z⁆ with hudef
    set w : G := ⁅(δ : G), z⁆ with hwdef
    set κ : G := ⁅g, w⁆ with hκdef
    set x' : G := ((δ : G) * g) * ⁅((δ : G) * g)⁻¹ * (g * (δ : G)), z⁆ * ((δ : G) * g)⁻¹ with hx'def
    have hnu := commutator_g_conj_eq hYc hVc hV2 hg3 hgY (fun v hv => hVn g hgM v hv) hzY hu
    have hnκ := commutator_g_conj_eq hYc hVc hV2 hg3 hgY (fun v hv => hVn g hgM v hv) hwY hκV
    have hnu' : ⁅g, g * u * g⁻¹⁆ = u := hnu
    have hnκ' : ⁅g, g * κ * g⁻¹⁆ = κ := hnκ
    have hv₂ : g * u * g⁻¹ ∈ blockV S L := hVn g hgM u hu
    have hv₁ : g * κ * g⁻¹ ∈ blockV S L := hVn g hgM κ hκV
    have huX : u ∈ ⁅blockV S L, L⁆ := by
      have := hgX _ hv₂; rwa [hnu'] at this
    have hκX : κ ∈ ⁅blockV S L, L⁆ := by
      have := hgX _ hv₁; rwa [hnκ'] at this
    have hδu : ⁅(δ : G), u⁆ ∈ ⁅blockV S L, L⁆ := by
      rw [commutatorElement_def]
      exact ⁅blockV S L, L⁆.mul_mem (hXn δ hδM u huX) (⁅blockV S L, L⁆.inv_mem huX)
    have hx'eq : x' = κ * ⁅(δ : G), u⁆⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]; exact hrel.symm
    have hx'X : x' ∈ ⁅blockV S L, L⁆ := by
      rw [hx'eq]; exact ⁅blockV S L, L⁆.mul_mem hκX (⁅blockV S L, L⁆.inv_mem hδu)
    have hx'L : ∀ l ∈ L, l * x' = x' * l := by
      intro l hl
      have hδgM : (δ : G) * g ∈ L ⊔ S := (L ⊔ S).mul_mem hδM hgM
      have hl' : ((δ : G) * g)⁻¹ * l * ((δ : G) * g) ∈ L := by
        have := (Subgroup.mem_normalizer_iff.1 (hML ((L ⊔ S).inv_mem hδgM)) l).1 hl
        simpa using this
      have hc := hXL z hz kM hkθ _ hl'
      rw [hkdef] at hc
      calc l * x' = ((δ : G) * g) * (((δ : G) * g)⁻¹ * l * ((δ : G) * g) *
            ⁅((δ : G) * g)⁻¹ * (g * (δ : G)), z⁆) * ((δ : G) * g)⁻¹ := by
            rw [hx'def]; group
        _ = ((δ : G) * g) * (⁅((δ : G) * g)⁻¹ * (g * (δ : G)), z⁆ *
              (((δ : G) * g)⁻¹ * l * ((δ : G) * g))) * ((δ : G) * g)⁻¹ := by rw [hc]
        _ = x' * l := by rw [hx'def]; group
    have hx'Kr : x' ∈ ⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨hx'X, Subgroup.mem_centralizer_iff.2 hx'L⟩
    have hx'1 : π ⟨x', hx'X⟩ = 1 := by
      have : (⟨x', hx'X⟩ : ↥⁅blockV S L, L⁆) ∈ π.ker := by
        rw [hker, Subgroup.mem_subgroupOf]; exact hx'Kr
      exact MonoidHom.mem_ker.1 this
    set v₁ : G := g * κ * g⁻¹ with hv₁def
    have hv₁X : v₁ ∈ ⁅blockV S L, L⁆ := hXn g hgM κ hκX
    have hgv₁ : g * v₁ * g⁻¹ = κ * v₁ := by
      have h : ⁅g, v₁⁆ = κ := hnκ
      rw [commutatorElement_def] at h
      calc g * v₁ * g⁻¹ = (g * v₁ * g⁻¹ * v₁⁻¹) * v₁ := by group
        _ = κ * v₁ := by rw [h]
    have hδu' : (δ : G) * u * (δ : G)⁻¹ = ⁅(δ : G), u⁆ * u := by
      rw [commutatorElement_def]; group
    have hrel' : (g * v₁ * g⁻¹) * u = x' * (((δ : G) * u * (δ : G)⁻¹) * v₁) := by
      have hVu : v₁ * u = u * v₁ := hVc _ hv₁ u hu
      have h1 : κ = x' * ⁅(δ : G), u⁆ := hrel
      calc (g * v₁ * g⁻¹) * u = κ * (v₁ * u) := by rw [hgv₁, mul_assoc]
        _ = κ * (u * v₁) := by rw [hVu]
        _ = (x' * ⁅(δ : G), u⁆) * (u * v₁) := by rw [← h1]
        _ = x' * (((δ : G) * u * (δ : G)⁻¹) * v₁) := by rw [hδu']; group
    obtain ⟨hδuX, hπδu⟩ := pi_commutator_eq_one_of_rel_mul π θ hequiv hgM hδM hXn huX hv₁X hx'X
      hx'1 hrel' hd T Γ hTc hΓc hTΓ hcT hfΓ
    have hδuKr : ⁅(δ : G), u⁆ ∈ ⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G) := by
      have : (⟨⁅(δ : G), u⁆, hδuX⟩ : ↥⁅blockV S L, L⁆) ∈ π.ker := hπδu
      rw [hker, Subgroup.mem_subgroupOf] at this
      exact this
    have hκKr : κ ∈ ⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G) := by
      have h1 : κ = x' * ⁅(δ : G), u⁆ := hrel
      rw [h1]
      exact Subgroup.mul_mem _ hx'Kr hδuKr
    have hgκ : g * κ * g⁻¹ = κ := by
      have := Subgroup.mem_centralizer_iff.1 hκKr.2 g hgL
      calc g * κ * g⁻¹ = κ * g * g⁻¹ := by rw [this]
        _ = κ := by group
    have hgw : g * w * g⁻¹ = κ * w := by rw [hκdef, commutatorElement_def]; group
    have hκ1 : κ = 1 := eq_one_of_conj_eq_mul hgw hgκ (hV2 κ hκV) hm hgm
    rw [hgw, hκ1, one_mul]
  let E : Subgroup G := Subgroup.closure {x | ∃ δ : ↥(L ⊔ S), (δ : G) ∈ S ∧
    (∀ p, θ' δ (Sum.inl p) = Sum.inl p) ∧ θ' δ ∈ alternatingGroup (OmegaE r 4) ∧
      ∃ z ∈ Z₀, x = ⁅(δ : G), z⁆}
  have hEg : ∀ x ∈ E, g * x * g⁻¹ = x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨δ, hδS, hδfix, hδalt, z, hz, rfl⟩ := hy
      exact hkey δ hδS hδfix hδalt z hz
    | one => simp
    | mul y z _ _ hy hz =>
      have : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
      rw [this, hy, hz]
    | inv y _ hy =>
      have : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
      rw [this, hy]
  have hCS : ⁅Z₀, S⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro z hz s hs
    rw [commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem (hZS hz) hs) (S.inv_mem (hZS hz))) (S.inv_mem hs)
  have hCE : ⁅Z₀, S⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro z hz s hs
    obtain ⟨j, hjJ, δ, hδS, hδfix, hδalt, rfl⟩ := hdecomp s hs
    have hzj : Commute (j : G) z :=
      (Subgroup.mem_centralizer_iff.1
        ((CFSG.Quasithin.C1GN.omegaOneCenterOf_le_centerOf _ hz).2) j hjJ)
    have hjz : j * z⁻¹ = z⁻¹ * j := hzj.inv_right.eq
    have hz' : ⁅z, (δ : G) * j⁆ = ⁅z, (δ : G)⁆ := by
      calc ⁅z, (δ : G) * j⁆ = z * (δ : G) * (j * z⁻¹) * j⁻¹ * (δ : G)⁻¹ := by
            rw [commutatorElement_def]; group
        _ = z * (δ : G) * (z⁻¹ * j) * j⁻¹ * (δ : G)⁻¹ := by rw [hjz]
        _ = ⁅z, (δ : G)⁆ := by rw [commutatorElement_def]; group
    rw [hz', ← commutatorElement_inv]
    exact E.inv_mem (Subgroup.subset_closure ⟨δ, hδS, hδfix, hδalt, z, hz, rfl⟩)
  have hCchar : ((⁅Z₀, S⁆).subgroupOf S).Characteristic :=
    characteristic_commutator_subgroupOf hZS hZchar
  have hgN : g ∈ Subgroup.normalizer (S : Set G) :=
    mem_normalizer_of_char_commute hA hCS hne hCchar hgM (fun x hx => hEg x (hCE hx))
  have hgW := theta_mem_normalizer_W θ' ⟨g, hgM⟩ hgN
  rw [hW, hgθ] at hgW
  exact hcN hgW

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
