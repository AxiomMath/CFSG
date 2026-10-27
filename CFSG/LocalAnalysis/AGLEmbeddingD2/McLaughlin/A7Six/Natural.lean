module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.Alt7FourFinish
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7Dim

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Six

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open scoped commutatorElement Pointwise

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

omit [Finite X] in
theorem commutator_self_of_alt7 {G : Type*} [Group G] {L : Subgroup G}
    (eL : ↥L ≃* alternatingGroup (Fin 7)) : ⁅L, L⁆ = L := by
  have hsimp : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hLs : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hcard : Nat.card ↥L = 2520 := by
    rw [Nat.card_congr eL.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hle : ⁅L, L⁆ ≤ L := Subgroup.commutator_le.2 fun a ha b hb =>
    L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)
  have hN : (⁅L, L⁆.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2
      (Subgroup.normalizer_commutator_ge_left L L)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅L, L⁆.subgroupOf L) with h | h
  · exfalso
    have hcomm : ∀ a b : ↥L, a * b = b * a := by
      intro a b
      have h1 : (⟨⁅(a : G), (b : G)⁆, hle (Subgroup.commutator_mem_commutator a.2 b.2)⟩ : ↥L) ∈
          ⁅L, L⁆.subgroupOf L := Subgroup.commutator_mem_commutator a.2 b.2
      rw [h, Subgroup.mem_bot] at h1
      have h2 : ⁅(a : G), (b : G)⁆ = 1 := congrArg Subtype.val h1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      rw [commutatorElement_eq_one_iff_mul_comm] at h2
      exact h2
    let _ : CommGroup ↥L := { (inferInstance : Group ↥L) with mul_comm := hcomm }
    have := IsSimpleGroup.prime_card (α := ↥L)
    rw [hcard] at this
    exact absurd this (by norm_num)
  · refine le_antisymm hle fun x hx => ?_
    have : (⟨x, hx⟩ : ↥L) ∈ ⁅L, L⁆.subgroupOf L := h ▸ Subgroup.mem_top _
    exact this

theorem commutator_trivial_of_central {W K C : Subgroup X}
    (hKc : ∀ k ∈ K, ∀ m ∈ ⁅W, K⁆, k * m = m * k)
    (hab : ∀ a ∈ ⁅W, K⁆, ∀ b ∈ ⁅W, K⁆, a * b = b * a)
    (hCW : ∀ c ∈ C, ∀ w ∈ W, c * w = w * c) (hK : K ≤ ⁅K, K⁆ ⊔ C)
    (hCN : C.Normal) : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ = w := by
  intro k₀ hk₀ w hw
  have hfm : ∀ k ∈ K, k * w * k⁻¹ * w⁻¹ ∈ ⁅W, K⁆ := by
    intro k hk
    have := Subgroup.commutator_mem_commutator (G := X) hw hk
    have e : k * w * k⁻¹ * w⁻¹ = (⁅w, k⁆)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.inv_mem _ this
  let f : ↥K →* ↥(⁅W, K⁆ : Subgroup X) :=
    { toFun := fun k => ⟨k * w * k⁻¹ * w⁻¹, hfm k k.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have h1 := hKc a a.2 _ (hfm b b.2)
        have h2 := hab _ (hfm b b.2) _ (hfm a a.2)
        calc (a : X) * b * w * ((a : X) * b)⁻¹ * w⁻¹ =
            (a : X) * ((b : X) * w * (b : X)⁻¹ * w⁻¹) * (a : X)⁻¹ *
              ((a : X) * w * (a : X)⁻¹ * w⁻¹) := by group
          _ = ((b : X) * w * (b : X)⁻¹ * w⁻¹) * (a : X) * (a : X)⁻¹ *
              ((a : X) * w * (a : X)⁻¹ * w⁻¹) := by rw [h1]
          _ = ((b : X) * w * (b : X)⁻¹ * w⁻¹) * ((a : X) * w * (a : X)⁻¹ * w⁻¹) := by group
          _ = ((a : X) * w * (a : X)⁻¹ * w⁻¹) * ((b : X) * w * (b : X)⁻¹ * w⁻¹) := h2 }
  set Kf : Subgroup X := f.ker.map K.subtype
  have hcommK : ⁅K, K⁆ ≤ Kf := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hab' : ⁅a, b⁆ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
    refine ⟨⟨⁅a, b⁆, hab'⟩, ?_, rfl⟩
    show _ ∈ f.ker
    rw [MonoidHom.mem_ker]
    have e : (⟨⁅a, b⁆, hab'⟩ : ↥K) = ⁅(⟨a, ha⟩ : ↥K), ⟨b, hb⟩⁆ := rfl
    rw [e, map_commutatorElement]
    apply Subtype.ext
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    have := hab _ (f ⟨a, ha⟩).2 _ (f ⟨b, hb⟩).2
    calc ((f ⟨a, ha⟩ : ↥(⁅W, K⁆ : Subgroup X)) : X) * ((f ⟨b, hb⟩ : ↥(⁅W, K⁆ : Subgroup X)) : X) *
          ((f ⟨a, ha⟩ : ↥(⁅W, K⁆ : Subgroup X)) : X)⁻¹ *
          ((f ⟨b, hb⟩ : ↥(⁅W, K⁆ : Subgroup X)) : X)⁻¹ =
        ((f ⟨b, hb⟩ : ↥(⁅W, K⁆ : Subgroup X)) : X) * ((f ⟨a, ha⟩ : ↥(⁅W, K⁆ : Subgroup X)) : X) *
          ((f ⟨a, ha⟩ : ↥(⁅W, K⁆ : Subgroup X)) : X)⁻¹ *
          ((f ⟨b, hb⟩ : ↥(⁅W, K⁆ : Subgroup X)) : X)⁻¹ := by rw [this]
      _ = 1 := by group
  have hCK : ∀ c ∈ C, c ∈ K → c ∈ Kf := by
    intro c hc hcK
    refine ⟨⟨c, hcK⟩, ?_, rfl⟩
    show _ ∈ f.ker
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show c * w * c⁻¹ * w⁻¹ = 1
    rw [hCW c hc w hw]; group
  have hk := hK hk₀
  have hmul : ((⁅K, K⁆ : Subgroup X) : Set X) * (C : Set X) =
      ((⁅K, K⁆ ⊔ C : Subgroup X) : Set X) :=
    (Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (fun x _ => (Subgroup.normalizer_eq_top_iff.mpr hCN).symm ▸ Subgroup.mem_top x)).symm
  have hk' : k₀ ∈ ((⁅K, K⁆ : Subgroup X) : Set X) * (C : Set X) := by rw [hmul]; exact hk
  obtain ⟨a, ha, c, hc, hac⟩ := hk'
  have hKK : ⁅K, K⁆ ≤ K := Subgroup.commutator_le.2 fun a ha b hb =>
    K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
  have haK : a ∈ K := hKK ha
  have hcK : c ∈ K := by
    have : c = a⁻¹ * k₀ := by rw [← hac]; group
    rw [this]
    exact K.mul_mem (K.inv_mem haK) hk₀
  have hkf : k₀ ∈ Kf := by
    rw [← hac]
    exact Kf.mul_mem (hcommK ha) (hCK c hc hcK)
  obtain ⟨y, hy1, hy⟩ := hkf
  have hy1' : f y = 1 := hy1
  clear hy1
  have hy1 := hy1'
  have hy' : y = ⟨k₀, hk₀⟩ := Subtype.ext hy
  rw [hy'] at hy1
  have h2 : k₀ * w * k₀⁻¹ * w⁻¹ = 1 := congrArg Subtype.val hy1
  calc k₀ * w * k₀⁻¹ = k₀ * w * k₀⁻¹ * w⁻¹ * w := by group
    _ = w := by rw [h2, one_mul]

theorem le_commutator_sup_gnC (L : Subgroup (X ⧸ gnC T)) (eL : ↥L ≃* alternatingGroup (Fin 7)) :
    L.comap (QuotientGroup.mk' (gnC T)) ≤
      ⁅L.comap (QuotientGroup.mk' (gnC T)), L.comap (QuotientGroup.mk' (gnC T))⁆ ⊔ gnC T := by
  set π := QuotientGroup.mk' (gnC T)
  set K := L.comap π
  have hKL : K.map π = L := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) L
  intro k hk
  have h1 : π k ∈ (⁅K, K⁆ : Subgroup X).map π := by
    rw [Subgroup.map_commutator, hKL, commutator_self_of_alt7 eL]
    exact hk
  obtain ⟨k', hk', hkk⟩ := h1
  have hc : k'⁻¹ * k ∈ gnC T := by
    rw [← QuotientGroup.ker_mk' (gnC T), MonoidHom.mem_ker, map_mul, map_inv, hkk, inv_mul_cancel]
  have : k = k' * (k'⁻¹ * k) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hk' hc

theorem relIndex_six_of_natural
    (hX : GNSetting X T) {C₁ C₂ : Subgroup X} (hP : IsC118Pair T C₁ C₂)
    {L : Subgroup (X ⧸ gnC T)} (hY : GNYComponent T C₁ C₂ L) (eL : ↥L ≃* alternatingGroup (Fin 7))
    (hn : FiveThreeAlt.A7NaturalCase T L) :
    (⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ ⊓
        Subgroup.centralizer (L.comap (QuotientGroup.mk' (gnC T)) : Set X)).relIndex
      ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ = 2 ^ 6 := by
  classical
  obtain ⟨-, h1Z, -, -, h2B, h2c, -⟩ := id hP
  have hJ := CFSG.AGLEmbeddingD2.GN.commutator_eq_of_gnYComponent hX h1Z h2B h2c hY
  set mk := QuotientGroup.mk' (gnC T)
  set K := L.comap mk
  set N := ⁅gnV T, K⁆
  obtain ⟨g, W, π, hg, hWV, hZW, hWK, hker, heq⟩ := hn
  have hMN : (⁅W, K⁆ : Subgroup X) ≤ N := Subgroup.commutator_mono hWV le_rfl
  have hQT := CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow
  obtain ⟨-, h46⟩ := FiveThreeAlt.a7_clause_dim T hX.charTwo hQT L hY.1 hJ eL
  have hMK : K ≤ Subgroup.normalizer ((⁅W, K⁆ : Subgroup X) : Set X) := Subgroup.normalizer_commutator_ge_right W K
  have hV := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.isElemAbelian_gnV T hX
  have hequiv : ∀ (l : X) (hl : mk l ∈ L) (u : ↥(⁅W, K⁆ : Subgroup X)) (hu : l * (u : X) * l⁻¹ ∈ (⁅W, K⁆ : Subgroup X)),
      Multiplicative.toAdd (π ⟨l * u * l⁻¹, hu⟩) =
        altAct (g ⟨mk l, hl⟩ : Equiv.Perm (Fin 7)) (Multiplicative.toAdd (π u)) := by
    intro l hl u hu
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (π u))
    rw [← hx, altAct_mk]
    exact heq l hl u ⟨_, hu⟩ rfl x hx.symm
  let U : AddSubgroup (altHeart 7) :=
    { carrier := {v | ∃ u : ↥(⁅W, K⁆ : Subgroup X), Multiplicative.toAdd (π u) = v}
      add_mem' := by
        rintro _ _ ⟨u, rfl⟩ ⟨u', rfl⟩
        exact ⟨u * u', by rw [map_mul, toAdd_mul]⟩
      zero_mem' := ⟨1, by rw [map_one, toAdd_one]⟩
      neg_mem' := by
        rintro _ ⟨u, rfl⟩
        exact ⟨u⁻¹, by rw [map_inv, toAdd_inv]⟩ }
  have hU : ∀ σ ∈ alternatingGroup (Fin 7), ∀ x : evenWeight 7,
      (QuotientAddGroup.mk x : altHeart 7) ∈ U →
        (QuotientAddGroup.mk (evenWeightPerm σ x) : altHeart 7) ∈ U := by
    rintro σ hσ x ⟨u, hux⟩
    obtain ⟨y, hy⟩ := hg ⟨σ, hσ⟩
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (y : X ⧸ gnC T)
    have hlL : mk l ∈ L := by
      show (QuotientGroup.mk l : X ⧸ gnC T) ∈ L
      rw [hl]; exact y.2
    have hlK : l ∈ K := hlL
    have hu' : l * (u : X) * l⁻¹ ∈ (⁅W, K⁆ : Subgroup X) := (Subgroup.mem_normalizer_iff.1 (hMK hlK) u).1 u.2
    refine ⟨⟨_, hu'⟩, ?_⟩
    rw [hequiv l hlL u hu', hux, altAct_mk]
    have hgy : g ⟨mk l, hlL⟩ = ⟨σ, hσ⟩ := by
      rw [← hy]
      congr 1
      exact Subtype.ext hl
    rw [hgy]
  rcases altHeart_irreducible (by norm_num) U hU with hbot | htop
  ·
    exfalso
    have hπ1 : ∀ u : ↥(⁅W, K⁆ : Subgroup X), π u = 1 := by
      intro u
      have : Multiplicative.toAdd (π u) ∈ U := ⟨u, rfl⟩
      rw [hbot, AddSubgroup.mem_bot] at this
      exact Multiplicative.toAdd.injective (this.trans toAdd_one.symm)
    have hKc : ∀ k ∈ K, ∀ m ∈ (⁅W, K⁆ : Subgroup X), k * m = m * k := by
      intro k hk m hm
      have := hker ⟨m, hm⟩ (hπ1 _) k hk
      calc k * m = k * m * k⁻¹ * k := by group
        _ = m * k := by rw [this]
    have hWKn : K ≤ Subgroup.normalizer (W : Set X) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · exact hWK k hk w
      · intro h
        have := hWK k⁻¹ (K.inv_mem hk) _ h
        simpa [mul_assoc] using this
    have hMW : (⁅W, K⁆ : Subgroup X) ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.1 hWKn
    have hab : ∀ a ∈ (⁅W, K⁆ : Subgroup X), ∀ b ∈ (⁅W, K⁆ : Subgroup X), a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hV.1.1.comm ⟨a, hWV (hMW ha)⟩ ⟨b, hWV (hMW hb)⟩)
    have hCW : ∀ c ∈ gnC T, ∀ w ∈ W, c * w = w * c := fun c hc w hw =>
      (Subgroup.mem_centralizer_iff.1 hc w (hWV hw)).symm
    have hcent := commutator_trivial_of_central hKc hab hCW (le_commutator_sup_gnC L eL)
      (gnC_normal T)
    apply hY.2.1
    intro y hy
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    have hlK : l ∈ K := hy
    refine ⟨l, Subgroup.mem_centralizer_iff.2 fun c hc => ?_, rfl⟩
    have h1 := hcent l hlK c (hZW (h1Z hc))
    calc c * l = l * c * l⁻¹ * l := by rw [h1]
      _ = l * c := by group
  ·
    have hsurj : Function.Surjective π := by
      intro v
      have : Multiplicative.toAdd v ∈ U := htop ▸ AddSubgroup.mem_top _
      obtain ⟨u, hu⟩ := this
      exact ⟨u, Multiplicative.toAdd.injective hu⟩
    have hkerπ : π.ker = ((⁅W, K⁆ : Subgroup X) ⊓ Subgroup.centralizer (K : Set X)).subgroupOf (⁅W, K⁆ : Subgroup X) := by
      ext u
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hu
        refine ⟨u.2, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
        have := hker u hu k hk
        calc k * (u : X) = k * (u : X) * k⁻¹ * k := by group
          _ = (u : X) * k := by rw [this]
      · rintro ⟨-, hc⟩
        obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (π u))
        have hfix : ∀ σ ∈ alternatingGroup (Fin 7),
            (QuotientAddGroup.mk (evenWeightPerm σ x) : altHeart 7) = QuotientAddGroup.mk x := by
          intro σ hσ
          obtain ⟨y, hy⟩ := hg ⟨σ, hσ⟩
          obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (y : X ⧸ gnC T)
          have hlL : mk l ∈ L := by
            show (QuotientGroup.mk l : X ⧸ gnC T) ∈ L
            rw [hl]; exact y.2
          have hlu : l * (u : X) * l⁻¹ = u := by
            have := Subgroup.mem_centralizer_iff.1 hc l hlL
            rw [this]; group
          have hu' : l * (u : X) * l⁻¹ ∈ (⁅W, K⁆ : Subgroup X) := by rw [hlu]; exact u.2
          have h1 := hequiv l hlL u hu'
          have e : (⟨l * (u : X) * l⁻¹, hu'⟩ : ↥(⁅W, K⁆ : Subgroup X)) = u := Subtype.ext hlu
          rw [e, ← hx, altAct_mk] at h1
          have hgy : g ⟨mk l, hlL⟩ = ⟨σ, hσ⟩ := by
            rw [← hy]
            congr 1
            exact Subtype.ext hl
          rw [hgy] at h1
          exact h1.symm
        have h0 := altHeart_fixed_eq_zero (by norm_num) x hfix
        rw [hx] at h0
        exact Multiplicative.toAdd.injective (h0.trans toAdd_one.symm)
    have hM : ((⁅W, K⁆ : Subgroup X) ⊓ Subgroup.centralizer (K : Set X)).relIndex (⁅W, K⁆ : Subgroup X) = 2 ^ 6 := by
      have h1 := Subgroup.index_ker π
      rw [hkerπ, MonoidHom.range_eq_top_of_surjective _ hsurj, Subgroup.card_top,
        Nat.card_congr Multiplicative.toAdd, FiveThreeAlt.card_altHeart_seven] at h1
      exact h1
    have hle : ((⁅W, K⁆ : Subgroup X) ⊓ Subgroup.centralizer (K : Set X)).relIndex (⁅W, K⁆ : Subgroup X) ≤
        (N ⊓ Subgroup.centralizer (K : Set X)).relIndex N := by
      have h1 : (N ⊓ Subgroup.centralizer (K : Set X)).relIndex (⁅W, K⁆ : Subgroup X) =
          ((⁅W, K⁆ : Subgroup X) ⊓ Subgroup.centralizer (K : Set X)).relIndex (⁅W, K⁆ : Subgroup X) := by
        rw [← Subgroup.inf_relIndex_right]
        congr 1
        exact le_antisymm (le_inf inf_le_right (inf_le_left.trans inf_le_right))
          (le_inf (le_inf (inf_le_left.trans hMN) inf_le_right) inf_le_left)
      rw [← h1]
      exact Subgroup.relIndex_le_of_le_right hMN
        (Subgroup.index_ne_zero_of_finite (H := (N ⊓ Subgroup.centralizer (K : Set X)).subgroupOf N))
    rcases h46 with h4 | h6
    · rw [hM, h4] at hle
      norm_num at hle
    · exact h6

end CFSG.AGLEmbeddingD2.McLaughlin.A7Six
