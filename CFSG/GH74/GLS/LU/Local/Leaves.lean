module

public import CFSG.GH74.GLS.LU.Local.Setup
public import CFSG.GH74.GLS.LU.Local.Gen

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS

variable {G : Type} [Group G]

theorem odd_orderOf_pPrimeCoreOf [Finite G] {X : Subgroup G} {a : G} (ha : a ∈ pPrimeCoreOf 2 X) :
    Odd (orderOf a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥X)) := pPrimeCore_coprime_card
  have hd : orderOf a' ∣ Nat.card (pPrimeCore 2 ↥X) := Subgroup.orderOf_dvd_natCard _ ha'
  have hodd : Odd (orderOf a') :=
    Nat.coprime_two_left.1 (Nat.Coprime.coprime_dvd_right hd hcop)
  have h2 : orderOf ((a' : ↥X) : G) = orderOf a' := Subgroup.orderOf_coe _
  rw [show (X.subtype a' : G) = ((a' : ↥X) : G) from rfl, h2]
  exact hodd

theorem normalizer_iSup_of {ι : Type*} (Y : ι → Subgroup G) {x : G}
    (hx : ∀ i, (Y i).map (MulAut.conj x).toMonoidHom = Y i) :
    x ∈ normalizer ((⨆ i, Y i : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_iSup]
  exact iSup_congr hx

namespace LUComps

variable {q : ℕ} {z : G} {K₁ K₂ : Subgroup G}

theorem odd_fix [Finite G] (h : LUComps G q z K₁ K₂) {c : G} (hc : c ∈ Cz z)
    (hodd : Odd (orderOf c)) :
    K₁.map (MulAut.conj c).toMonoidHom = K₁ ∧ K₂.map (MulAut.conj c).toMonoidHom = K₂ := by
  rcases h.perm hc with hfix | ⟨e1, e2⟩
  · exact hfix
  · exfalso
    have h1 : ∀ a ∈ K₁, c * a * c⁻¹ ∈ K₂ := fun a ha => mem_of_map e1 ha
    have h2 : ∀ a ∈ K₂, c * a * c⁻¹ ∈ K₁ := fun a ha => mem_of_map e2 ha
    have hle := odd_no_swap hodd h1 h2
    have hK₁le : K₁ ≤ zpowers z := by
      intro a ha
      rw [← h.inf_eq]
      exact ⟨ha, hle a ha⟩
    have hcomm : ⁅K₁, K₁⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (hK₁le ha)
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp (hK₁le hb)
      rw [Subgroup.mem_bot]
      have : z ^ i * z ^ j = z ^ j * z ^ i := (Commute.zpow_zpow_self z i j).eq
      simp [commutatorElement_def, this]
    have hbot : K₁ = ⊥ := by rw [← h.perfect₁, hcomm]
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial h.quasi₁
    exact (Subgroup.nontrivial_iff_ne_bot K₁).mp hnt hbot

end LUComps

namespace LUEps

variable {q : ℕ} {ε : ℤ} {z : G} {K₁ K₂ : Subgroup G} {S : Sylow 2 G} {t u : G}

theorem mul_z [Finite G] (he : LUEps G q ε z K₁ u) (hc : LUComps G q z K₁ K₂) :
    LUEps G q ε z K₁ (u * z) := by
  have hcent : K₁ ⊓ centralizer ({u * z} : Set G) = K₁ ⊓ centralizer ({u} : Set G) := by
    ext k
    constructor
    · rintro ⟨hk, hku⟩
      refine ⟨hk, ?_⟩
      have h1 : k * (u * z) = (u * z) * k := mem_centralizer_singleton_iff.mp hku
      have h2 := hc.cz₁ hk
      refine mem_centralizer_singleton_iff.mpr ?_
      calc k * u = k * u * z * z⁻¹ := by group
        _ = u * z * k * z⁻¹ := by rw [mul_assoc k u z, h1]
        _ = u * (z * k) * z⁻¹ := by group
        _ = u * (k * z) * z⁻¹ := by rw [h2]
        _ = u * k := by group
    · rintro ⟨hk, hku⟩
      refine ⟨hk, ?_⟩
      have h1 : k * u = u * k := mem_centralizer_singleton_iff.mp hku
      have h2 := hc.cz₁ hk
      refine mem_centralizer_singleton_iff.mpr ?_
      calc k * (u * z) = (k * u) * z := by group
        _ = (u * k) * z := by rw [h1]
        _ = u * (k * z) := by group
        _ = u * (z * k) := by rw [h2]
        _ = (u * z) * k := by group
  refine ⟨he.eps, he.mod8, he.A0_cyc, he.A0_dvd, ?_, ?_⟩
  · rw [hcent]; exact he.H_cyc
  · rw [hcent]; exact he.H_card

end LUEps

structure LU61 (G : Type) [Group G] (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G) : Prop where
  t_inv : ∀ a ∈ A0 z, t * a * t⁻¹ = a⁻¹
  u_cent : ∀ a ∈ A0 z, u * a * u⁻¹ = a
  A0_le : A0 z ≤ Fstar (S : Subgroup G) K₁ K₂ u
  u_norm_J : ∃ g : G, g⁻¹ * z * g = t ∧ (∀ a ∈ cj K₁ g, u * a * u⁻¹ ∈ cj K₁ g) ∧
    (∀ a ∈ cj K₂ g, u * a * u⁻¹ ∈ cj K₂ g)

theorem normalize_u
    [Finite G] {q p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t u : G}
    (hG : IsKProperSimple G) (hp : p.Prime) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ f)
    (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u) (hcyc : IsCyclic ↥(A0 z))
    (h6A : MaxOverCentralizerPSp4 z p f) :
    ∃ u₀ : G, (u₀ = u ∨ u₀ = u * z) ∧ LUSyl G z S K₁ K₂ t u₀ ∧ LU61 G z S K₁ K₂ t u₀ := by
  have hsimple : IsSimpleGroup G := hG.1
  have hnab := hG.2.1
  have := hcyc
  obtain ⟨cc, hcc⟩ := isConj_iff.mp hs.t_conj
  have hg : (cc⁻¹)⁻¹ * z * cc⁻¹ = t := by rw [inv_inv]; exact hcc
  have key : ∀ u₀ : G, LUSyl G z S K₁ K₂ t u₀ →
      ((∀ a ∈ cj K₁ cc⁻¹, u₀ * a * u₀⁻¹ ∈ cj K₁ cc⁻¹) ∧
        (∀ a ∈ cj K₂ cc⁻¹, u₀ * a * u₀⁻¹ ∈ cj K₂ cc⁻¹)) → LU61 G z S K₁ K₂ t u₀ := by
    intro u₀ hs₀ hnorm
    have htn : t ∉ normalizer (K₁ : Set G) := hs₀.t_not_normalizer hc
    exact ⟨lemma62a hsimple hnab hp hp2 hq5 hc hs₀ h6A hs₀.t_mem htn hs₀.t_conj,
      lemma62b hsimple hnab hp hp2 hq5 hc hs₀ h6A, lemma62c hsimple hnab hp hp2 hq5 hc hs₀ h6A,
      ⟨cc⁻¹, hg, hnorm⟩⟩
  rcases prop61a hc hs hg with hn | hn
  · exact ⟨u, Or.inl rfl, hs, key u hs hn⟩
  · exact ⟨u * z, Or.inr rfl, hs.mul_z hc, key (u * z) (hs.mul_z hc) hn⟩

@[expose] def LUGenLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ p f : ℕ, p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ∀ (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G) (ε : ℤ), LUComps G (p ^ f) z K₁ K₂ →
      LUSyl G z S K₁ K₂ t u → LUEps G (p ^ f) ε z K₁ u → MaxOverCentralizerPSp4 z p f →
      LU61 G z S K₁ K₂ t u →
      ∀ c ∈ Cz z, ∃ a ∈ A0 z, ∃ k ∈ K₁ ⊔ K₂, ∃ s ∈ (S : Subgroup G),
        ∃ y ∈ Fstar (S : Subgroup G) K₁ K₂ u, c = a * k * s * y

@[expose] def LUA3Leaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ p f : ℕ, p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ∀ (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G), LUComps G (p ^ f) z K₁ K₂ →
      LUSyl G z S K₁ K₂ t u → MaxOverCentralizerPSp4 z p f → LU61 G z S K₁ K₂ t u →
      (∀ c ∈ Cz z, ∃ a ∈ A0 z, ∃ k ∈ K₁ ⊔ K₂, ∃ s ∈ (S : Subgroup G),
        ∃ y ∈ Fstar (S : Subgroup G) K₁ K₂ u, c = a * k * s * y) →
      (LUEps G (p ^ f) 1 z K₁ u →
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (u' : G) (Y : Fin 3 → Subgroup G) (h : G),
          Nat.card K = p ^ f ∧ (u' = u ∨ u' = u * z) ∧ Y 0 = K₁ ∧ Y 2 = K₂ ∧ h⁻¹ * z * h = u' ∧
          (Y 1 = cj K₁ h ∨ Y 1 = cj K₂ h) ∧ IsLinearA3Neighborhood K z u' Y ∧
          ∃ T : Subgroup G, T ≤ (⨆ i, Y i : Subgroup G) ⊓ Cz z ∧ IsPGroup 2 T ∧
            Nat.card (S : Subgroup G) ≤ Nat.card T) ∧
      (LUEps G (p ^ f) (-1) z K₁ u →
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K p) (F : Type) (_ : Field F)
          (_ : Finite F) (u' : G) (Y : Fin 3 → Subgroup G) (h : G),
          Nat.card K = (p ^ f) ^ 2 ∧ Nat.card F = p ^ f ∧ (u' = u ∨ u' = u * z) ∧ Y 0 = K₁ ∧
          Y 2 = K₂ ∧ h⁻¹ * z * h = u' ∧ (Y 1 = cj K₁ h ∨ Y 1 = cj K₂ h) ∧
          IsUnitaryA3Neighborhood (p ^ f) K F z u' Y ∧
          ∃ T : Subgroup G, T ≤ (⨆ i, Y i : Subgroup G) ⊓ Cz z ∧ IsPGroup 2 T ∧
            Nat.card (S : Subgroup G) ≤ Nat.card T)

theorem luGenLeaf_of_sl2 (hK : SL2SylowLeaf) : LUGenLeaf := by
  intro G _ _ _ p f hp hp2 hq z S K₁ K₂ t u ε hc hs he _ h61
  have : IsCyclic ↥(A0 z) := he.A0_cyc
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  exact lu_gen_of_sl2 hK hc hs.toGen hodd hq h61.u_cent

theorem lu_F5 [Finite G] {q : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t u : G}
    (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u) (h61 : LU61 G z S K₁ K₂ t u)
    (hgen : ∀ c ∈ Cz z, ∃ a ∈ A0 z, ∃ k ∈ K₁ ⊔ K₂, ∃ s ∈ (S : Subgroup G),
      ∃ y ∈ Fstar (S : Subgroup G) K₁ K₂ u, c = a * k * s * y)
    {u' : G} (hu' : u' = u ∨ u' = u * z) {Y : Fin 3 → Subgroup G} (hY0 : Y 0 = K₁) (hY2 : Y 2 = K₂)
    {h : G} (hh : h⁻¹ * z * h = u') (hY1 : Y 1 = cj K₁ h ∨ Y 1 = cj K₂ h) {T : Subgroup G}
    (hTG : T ≤ (⨆ i, Y i : Subgroup G)) (hTC : T ≤ Cz z) (hTp : IsPGroup 2 T)
    (hTc : Nat.card (S : Subgroup G) ≤ Nat.card T) :
    Cz z ≤ normalizer ((⨆ i, Y i : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set G₀ : Subgroup G := ⨆ i, Y i with hG₀
  have hSC : (S : Subgroup G) ≤ Cz z := hs.S_le_Cz
  have hcu : LUComps G q u' (cj K₁ h) (cj K₂ h) := by
    have := hc.cj h
    rwa [hh] at this
  have hnorm : ∀ x : G, Odd (orderOf x) → x ∈ Cz z → x ∈ Cz u' → x ∈ normalizer (G₀ : Set G) := by
    intro x hodd hxz hxu
    obtain ⟨hx1, hx2⟩ := hc.odd_fix hxz hodd
    obtain ⟨hl1, hl2⟩ := hcu.odd_fix hxu hodd
    have h0 : (Y 0).map (MulAut.conj x).toMonoidHom = Y 0 := by rw [hY0]; exact hx1
    have h1 : (Y 1).map (MulAut.conj x).toMonoidHom = Y 1 := by
      rcases hY1 with e | e <;> rw [e]
      · exact hl1
      · exact hl2
    have h2 : (Y 2).map (MulAut.conj x).toMonoidHom = Y 2 := by rw [hY2]; exact hx2
    apply normalizer_iSup_of
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hAu : ∀ a ∈ A0 z, a ∈ Cz u' := by
    intro a ha
    have h1 : a * u = u * a := by
      have := h61.u_cent a ha
      calc a * u = (u * a * u⁻¹) * u := by rw [this]
        _ = u * a := by group
    have h2 : a * z = z * a := mem_centralizer_singleton_iff.mp (Subgroup.map_subtype_le _ ha)
    rw [mem_centralizer_singleton_iff]
    rcases hu' with rfl | rfl
    · exact h1
    · calc a * (u * z) = (a * u) * z := by group
        _ = (u * a) * z := by rw [h1]
        _ = u * (a * z) := by group
        _ = u * (z * a) := by rw [h2]
        _ = (u * z) * a := by group
  have hFcz : ∀ y ∈ Fstar (S : Subgroup G) K₁ K₂ u, y ∈ Cz z ∧ y ∈ Cz u' := by
    intro y hy
    have hyC : y ∈ centralizer (((S : Subgroup G) ⊓ (K₁ ⊔ K₂) ⊔ zpowers u : Subgroup G) : Set G) :=
      Subgroup.map_subtype_le _ hy
    have hzP : z ∈ ((S : Subgroup G) ⊓ (K₁ ⊔ K₂) ⊔ zpowers u : Subgroup G) :=
      Subgroup.mem_sup_left ⟨hs.z_mem, Subgroup.mem_sup_left hc.z_mem₁⟩
    have huP : u ∈ ((S : Subgroup G) ⊓ (K₁ ⊔ K₂) ⊔ zpowers u : Subgroup G) :=
      Subgroup.mem_sup_right (mem_zpowers u)
    have hyz : y * z = z * y := (mem_centralizer_iff.mp hyC z hzP).symm
    have hyu : y * u = u * y := (mem_centralizer_iff.mp hyC u huP).symm
    refine ⟨mem_centralizer_singleton_iff.mpr hyz, ?_⟩
    rw [mem_centralizer_singleton_iff]
    rcases hu' with rfl | rfl
    · exact hyu
    · calc y * (u * z) = (y * u) * z := by group
        _ = (u * y) * z := by rw [hyu]
        _ = u * (y * z) := by group
        _ = u * (z * y) := by rw [hyz]
        _ = (u * z) * y := by group
  set R : Subgroup G := A0 z ⊔ (K₁ ⊔ K₂) ⊔ Fstar (S : Subgroup G) K₁ K₂ u with hR
  have hA0R : A0 z ≤ R := (le_sup_left : A0 z ≤ A0 z ⊔ (K₁ ⊔ K₂)).trans le_sup_left
  have hKR : K₁ ⊔ K₂ ≤ R := (le_sup_right : K₁ ⊔ K₂ ≤ A0 z ⊔ (K₁ ⊔ K₂)).trans le_sup_left
  have hFR : Fstar (S : Subgroup G) K₁ K₂ u ≤ R := le_sup_right
  have hKG : K₁ ⊔ K₂ ≤ G₀ := by
    refine sup_le ?_ ?_
    · rw [← hY0]; exact le_iSup Y 0
    · rw [← hY2]; exact le_iSup Y 2
  have hRN : R ≤ normalizer (G₀ : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro a ha
      exact hnorm a (odd_orderOf_pPrimeCoreOf ha) (Subgroup.map_subtype_le _ ha) (hAu a ha)
    · exact hKG.trans Subgroup.le_normalizer
    · intro y hy
      exact hnorm y (odd_orderOf_pPrimeCoreOf hy) (hFcz y hy).1 (hFcz y hy).2
  have hCRS : ∀ c ∈ Cz z, ∃ r ∈ R, ∃ s ∈ (S : Subgroup G), c = r * s := by
    intro c hcC
    obtain ⟨a, ha, k, hk, s, hsS, y, hy, hcinv⟩ := hgen c⁻¹ (Subgroup.inv_mem _ hcC)
    have hsC : s ∈ Cz z := hSC hsS
    have hsinv : s⁻¹ ∈ Cz z := Subgroup.inv_mem _ hsC
    have hk' : s⁻¹ * k⁻¹ * s⁻¹⁻¹ ∈ K₁ ⊔ K₂ := hc.conj_sup_mem hsinv (Subgroup.inv_mem _ hk)
    have ha' : s⁻¹ * a⁻¹ * s⁻¹⁻¹ ∈ A0 z := A0_conj hsinv (Subgroup.inv_mem _ ha)
    refine ⟨y⁻¹ * (s⁻¹ * k⁻¹ * s⁻¹⁻¹) * (s⁻¹ * a⁻¹ * s⁻¹⁻¹),
      R.mul_mem (R.mul_mem (R.inv_mem (hFR hy)) (hKR hk')) (hA0R ha'), s⁻¹,
      (S : Subgroup G).inv_mem hsS, ?_⟩
    have : c = (c⁻¹)⁻¹ := (inv_inv c).symm
    rw [this, hcinv]
    group
  exact fun c hc => (le_normalizer_of_sylow_trick S hSC (fun r hr => hRN hr) hCRS hTG hTC hTp
    hTc).2 c hc

theorem luLocalLeaf_of_leaves
    (hGen : LUGenLeaf) (hA3 : LUA3Leaf) : LULocalLeaf := by
  intro G _ _ hG p f hp hp2 hq z S K₁ K₂ t u hc hs h6A
  constructor
  · intro he
    obtain ⟨u₀, hu₀, hs₀, h61⟩ := normalize_u hG hp hp2 hq hc hs he.A0_cyc h6A
    have he₀ : LUEps G (p ^ f) 1 z K₁ u₀ := by
      rcases hu₀ with rfl | rfl
      · exact he
      · exact he.mul_z hc
    have hgen := hGen G hG p f hp hp2 hq z S K₁ K₂ t u₀ 1 hc hs₀ he₀ h6A h61
    obtain ⟨K, hK, hKf, u', Y, h, hKc, hu', hY0, hY2, hh, hY1, hA, T, hT, hTp, hTc⟩ :=
      (hA3 G hG p f hp hp2 hq z S K₁ K₂ t u₀ hc hs₀ h6A h61 hgen).1 he₀
    refine ⟨K, hK, hKf, u', Y, hKc, hA, ?_⟩
    exact lu_F5 hc hs₀ h61 hgen (u := u₀) hu' hY0 hY2 hh hY1 (fun x hx => (hT hx).1) (fun x hx => (hT hx).2) hTp hTc
  · intro he
    obtain ⟨u₀, hu₀, hs₀, h61⟩ := normalize_u hG hp hp2 hq hc hs he.A0_cyc h6A
    have he₀ : LUEps G (p ^ f) (-1) z K₁ u₀ := by
      rcases hu₀ with rfl | rfl
      · exact he
      · exact he.mul_z hc
    have hgen := hGen G hG p f hp hp2 hq z S K₁ K₂ t u₀ (-1) hc hs₀ he₀ h6A h61
    obtain ⟨K, hK, hKf, hKp, F, hF, hFf, u', Y, h, hKc, hFc, hu', hY0, hY2, hh, hY1, hA, T, hT,
      hTp, hTc⟩ := (hA3 G hG p f hp hp2 hq z S K₁ K₂ t u₀ hc hs₀ h6A h61 hgen).2 he₀
    refine ⟨K, hK, hKf, hKp, F, hF, hFf, u', Y, hKc, hFc, hA, ?_⟩
    exact lu_F5 hc hs₀ h61 hgen (u := u₀) hu' hY0 hY2 hh hY1 (fun x hx => (hT hx).1) (fun x hx => (hT hx).2) hTp hTc

theorem luNeighborhood_of_leaves
    (hM : LUModelLeaf) (hGen : LUGenLeaf) (hA3 : LUA3Leaf)
    (h6A : LUMax6A) : LUNeighborhood :=
  luNeighborhood_of_model hM (luLocalLeaf_of_leaves hGen hA3) h6A

theorem luLocalLeaf_of_sl2
    (hK : SL2SylowLeaf) (hA3 : LUA3Leaf) : LULocalLeaf :=
  luLocalLeaf_of_leaves (luGenLeaf_of_sl2 hK) hA3

theorem luNeighborhood_of_sl2
    (hM : LUModelLeaf) (hK : SL2SylowLeaf) (hA3 : LUA3Leaf)
    (h6A : LUMax6A) : LUNeighborhood :=
  luNeighborhood_of_leaves hM (luGenLeaf_of_sl2 hK) hA3 h6A


end CFSG.GH74.GLS.LU.Local
