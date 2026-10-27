module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Am
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma5Mod
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma5Red
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4MinParabolic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace L1295A

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {n : ℕ} {V₁ H₁ : Subgroup G}

namespace Am_F4
open CFSG.Quasithin.H13.L1295A.Am_F4

variable (A : Am_F4 G T L V n V₁ H₁)

section Rep

variable {Vt : Type} [CommGroup Vt] (θ : ↥(A.Cs_F4 ⊔ A.Ls_F4) →* MulAut Vt)

@[expose] noncomputable def psi1_F4 : ↥H₁ →* MulAut Vt :=
  θ.comp ((A.rho_F4.comp (Subgroup.inclusion (le_sup_left : H₁ ≤ H₁ ⊔ lOne L V₁))).codRestrict _
    fun _ => A.rho_mem_sup_F4 _)

theorem psi1_apply_F4 (h : ↥H₁) :
    A.psi1_F4 θ h = θ ⟨A.rho_F4 (Subgroup.inclusion le_sup_left h), A.rho_mem_sup_F4 _⟩ := rfl

theorem conj_mem_Ls_F4 (x : ↥(H₁ ⊔ lOne L V₁)) {g} (hg : g ∈ A.Ls_F4) :
    A.rho_F4 x * g * (A.rho_F4 x)⁻¹ ∈ A.Ls_F4 := by
  obtain ⟨⟨l, hlH⟩, hl, rfl⟩ := hg
  have hl' : l ∈ lOne L V₁ := hl
  have h1 : (x : G) * l * (x : G)⁻¹ ∈ lOne L V₁ :=
    (Subgroup.mem_normalizer_iff.1 (A.nLOne_F4 x.2) l).1 hl'
  refine ⟨x * ⟨l, hlH⟩ * x⁻¹, h1, ?_⟩
  rw [map_mul, map_mul, map_inv]

theorem conj_mem_Cs_F4 (x : ↥(H₁ ⊔ lOne L V₁)) {c} (hc : c ∈ A.Cs_F4) :
    A.rho_F4 x * c * (A.rho_F4 x)⁻¹ ∈ A.Cs_F4 := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' := A.conj_mem_Ls_F4 x⁻¹ hk
  rw [map_inv, inv_inv] at hk'
  have h1 := Subgroup.mem_centralizer_iff.1 hc _ hk'
  calc k * (A.rho_F4 x * c * (A.rho_F4 x)⁻¹)
      = A.rho_F4 x * (((A.rho_F4 x)⁻¹ * k * A.rho_F4 x) * c) * (A.rho_F4 x)⁻¹ := by group
    _ = A.rho_F4 x * (c * ((A.rho_F4 x)⁻¹ * k * A.rho_F4 x)) * (A.rho_F4 x)⁻¹ := by rw [h1]
    _ = A.rho_F4 x * c * (A.rho_F4 x)⁻¹ * k := by group

variable {θ}

theorem theta_rho_mem_range_F4 (hθL : ∀ l (hl : l ∈ A.Ls_F4), θ ⟨l, Subgroup.mem_sup_right hl⟩ = 1)
    (x : ↥(H₁ ⊔ lOne L V₁)) : θ ⟨A.rho_F4 x, A.rho_mem_sup_F4 x⟩ ∈ (A.psi1_F4 θ).range := by
  have hx : (x : G) ∈ ((H₁ ⊔ lOne L V₁ : Subgroup G) : Set G) := x.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ A.nL₁] at hx
  obtain ⟨h₁, hh₁, l, hl, hxe⟩ := hx
  have e : x = ⟨h₁, Subgroup.mem_sup_left hh₁⟩ * ⟨l, Subgroup.mem_sup_right hl⟩ :=
    Subtype.ext hxe.symm
  refine ⟨⟨h₁, hh₁⟩, ?_⟩
  rw [psi1_apply_F4]
  have hlLs : A.rho_F4 ⟨l, Subgroup.mem_sup_right hl⟩ ∈ A.Ls_F4 :=
    ⟨⟨l, Subgroup.mem_sup_right hl⟩, hl, rfl⟩
  have e2 : (⟨A.rho_F4 x, A.rho_mem_sup_F4 x⟩ : ↥(A.Cs_F4 ⊔ A.Ls_F4)) =
      ⟨A.rho_F4 ⟨h₁, Subgroup.mem_sup_left hh₁⟩, A.rho_mem_sup_F4 _⟩ *
        ⟨A.rho_F4 ⟨l, Subgroup.mem_sup_right hl⟩, Subgroup.mem_sup_right hlLs⟩ := by
    apply Subtype.ext
    show A.rho_F4 x = A.rho_F4 _ * A.rho_F4 _
    rw [e, map_mul]
  rw [e2, map_mul, hθL _ hlLs, mul_one]
  rfl

theorem pCoreOf_eq_bot_F4 [Finite Vt] (hθL : ∀ l (hl : l ∈ A.Ls_F4), θ ⟨l, Subgroup.mem_sup_right hl⟩ = 1)
    (hθinj : ∀ a (ha : a ∈ A.Cs_F4), θ ⟨a, Subgroup.mem_sup_left ha⟩ = 1 → a = 1) :
    pCoreOf 2 (⊤ : Subgroup ↥(A.psi1_F4 θ).range) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := (A.psi1_F4 θ).range with hX
  set Q := pCoreOf 2 (⊤ : Subgroup ↥X) with hQ
  set Q' := Q.map X.subtype with hQ'
  have hQn : Q.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (LieType.BorelTits.le_normalizer_pCoreOf 2 _))
  have hQ'X : ∀ y ∈ X, ∀ q ∈ Q', y * q * y⁻¹ ∈ Q' := by
    rintro y hy _ ⟨q, hq, rfl⟩
    exact ⟨⟨y, hy⟩ * q * ⟨y, hy⟩⁻¹, hQn.conj_mem q hq _, rfl⟩
  have hQ'2 : IsPGroup 2 Q' := (LieType.BorelTits.pCoreOf_isPGroup 2 _).map X.subtype

  set P : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))) :=
    (A.rho_F4.range ⊓ A.Cs_F4) ⊓ (Q'.comap θ).map (A.Cs_F4 ⊔ A.Ls_F4).subtype with hP
  have hmemP : ∀ c, c ∈ P ↔ c ∈ A.rho_F4.range ∧ ∃ hc : c ∈ A.Cs_F4,
      θ ⟨c, Subgroup.mem_sup_left hc⟩ ∈ Q' := by
    intro c
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨⟨c', hc'S⟩, hc'Q, rfl⟩⟩
      exact ⟨h1, h2, hc'Q⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, ⟨⟨c, Subgroup.mem_sup_left h2⟩, h3, rfl⟩⟩
  have hPbot : P = ⊥ := by
    rw [eq_bot_iff, ← A.pCoreOf_range_eq_bot_F4]
    refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (fun c hc => ((hmemP c).1 hc).1)
      (LinearS3.le_normalizer_of_conj_mem fun g hg c hc => ?_) ?_
    · obtain ⟨x, rfl⟩ := hg
      obtain ⟨hcR, hcC, hcQ⟩ := (hmemP c).1 hc
      refine (hmemP _).2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ ⟨x, rfl⟩ hcR)
        (Subgroup.inv_mem _ ⟨x, rfl⟩), A.conj_mem_Cs_F4 x hcC, ?_⟩
      have e : (⟨A.rho_F4 x * c * (A.rho_F4 x)⁻¹,
          Subgroup.mem_sup_left (A.conj_mem_Cs_F4 x hcC)⟩ : ↥(A.Cs_F4 ⊔ A.Ls_F4)) =
          ⟨A.rho_F4 x, A.rho_mem_sup_F4 x⟩ * ⟨c, Subgroup.mem_sup_left hcC⟩ *
            ⟨A.rho_F4 x, A.rho_mem_sup_F4 x⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact hQ'X _ (A.theta_rho_mem_range_F4 hθL x) _ hcQ
    · intro c
      obtain ⟨-, hcC, hcQ⟩ := (hmemP c).1 c.2
      obtain ⟨k, hk⟩ := hQ'2 ⟨_, hcQ⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : θ ⟨(c : MulAut _), Subgroup.mem_sup_left hcC⟩ ^ 2 ^ k = 1 := by
        simpa using congrArg Subtype.val hk
      rw [← map_pow] at h1
      have h2 : ((c : MulAut _) ^ 2 ^ k) ∈ A.Cs_F4 := Subgroup.pow_mem _ hcC _
      have h3 := hθinj _ h2 (by
        have e : (⟨(c : MulAut _) ^ 2 ^ k, Subgroup.mem_sup_left h2⟩ : ↥(A.Cs_F4 ⊔ A.Ls_F4)) =
            ⟨(c : MulAut _), Subgroup.mem_sup_left hcC⟩ ^ 2 ^ k := rfl
        rw [e]
        exact h1)
      simpa using h3

  have hQ'bot : Q' = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    have hqX : q ∈ X := by
      obtain ⟨q', -, rfl⟩ := hq
      exact q'.2
    obtain ⟨h₁, rfl⟩ := hqX
    rw [psi1_apply_F4] at hq ⊢
    set x := Subgroup.inclusion (le_sup_left : H₁ ≤ H₁ ⊔ lOne L V₁) h₁ with hx
    have hsup : A.rho_F4 x ∈ ((A.Cs_F4 ⊔ A.Ls_F4 : Subgroup _) : Set (MulAut _)) := A.rho_mem_sup_F4 x
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (Subgroup.centralizer_le_normalizer _)] at hsup
    obtain ⟨c, hc, l, hl, hcl⟩ := hsup
    have e : (⟨A.rho_F4 x, A.rho_mem_sup_F4 x⟩ : ↥(A.Cs_F4 ⊔ A.Ls_F4)) =
        ⟨c, Subgroup.mem_sup_left hc⟩ * ⟨l, Subgroup.mem_sup_right hl⟩ :=
      Subtype.ext hcl.symm
    rw [e, map_mul, hθL l hl, mul_one] at hq ⊢
    have hcR : c ∈ A.rho_F4.range := by
      obtain ⟨⟨l₀, hl₀H⟩, -, hl₀⟩ := hl
      refine ⟨x * ⟨l₀, hl₀H⟩⁻¹, ?_⟩
      rw [map_mul, map_inv, hl₀, ← hcl]
      group
    have hcP : c ∈ P := (hmemP c).2 ⟨hcR, hc, hq⟩
    rw [hPbot, Subgroup.mem_bot] at hcP
    subst hcP
    rw [Subgroup.mem_bot]
    exact map_one θ
  rw [hQ', Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective] at hQ'bot
  exact hQ'bot

end Rep

include A in

theorem false_of_F4 (h331 : Stmt3_3_1_F4) (hB : B69One) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd : 3 ≤ n - 1 := by rcases A.cx.n45 with h | h <;> omega
  have hUT := A.elemAb_F4
  let _ : CommGroup ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))) := commGroupOfElemAbelian hUT
  have hW : ∀ w : ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))), w ^ 2 = 1 :=
    fun w => Subtype.ext (by simpa using hUT.2 w w.2)

  obtain ⟨m, Vt, _, _, hsqV, hV, θ, hθL, hθinj, hcard, hcardW⟩ := Mult.exists_rep hW
    (fun l hl y hy => A.mapsTo_Yg_F4 hl hy) A.onto_Yg_F4 (by omega : 2 ≤ n - 1) A.card_Yg_F4
    A.span_eq_top_F4

  obtain ⟨B, hBL, hBH, hBel, hnt, -, hr⟩ := A.hF_F4.F916_3_aux
  rw [← lOne_eq_L₁Of] at hBL
  have hBT : B ≤ T := hBL.trans (pCoreOf_two_le_of_isSylowTwoOf
    (isSylowTwoOf_of_quasithinIsSylowTwo A.cx.hyp.hyp.sylow le_sup_right))
  have hBH₁ : B ≤ H₁ := hBT.trans A.T_le_F4
  have hBs : autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))) =
      (B.subgroupOf (H₁ ⊔ lOne L V₁)).map A.rho_F4 := A.autOn_eq_map_F4 hBH
  have hBsC : autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))) ≤ A.Cs_F4 := by
    rw [hBs]
    rintro _ ⟨⟨b, hbH⟩, hb, rfl⟩
    exact A.rho_mem_cent_of_le_F4 (hBL hb)

  have hq : Nat.card (autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))) =
      (B ⊓ pCoreOf 2 (H₁ ⊔ lOne L V₁)).relIndex B := A.hF_F4.toHypF91.card_autOn_tilde hBH
  have hq2 : 2 ≤ (B ⊓ pCoreOf 2 (H₁ ⊔ lOne L V₁)).relIndex B := by
    have h1 : (B ⊓ pCoreOf 2 (H₁ ⊔ lOne L V₁)).relIndex B ≠ 1 := fun h1 =>
      hnt ((Subgroup.relIndex_eq_one.1 h1).trans inf_le_right)
    have h2 : (B ⊓ pCoreOf 2 (H₁ ⊔ lOne L V₁)).relIndex B ≠ 0 := by
      intro h0
      have := Subgroup.relIndex_mul_card (B ⊓ pCoreOf 2 (H₁ ⊔ lOne L V₁)) B
      rw [h0, zero_mul] at this
      exact Nat.card_pos.ne' this.symm
    omega

  have hn' := HypF91.tilde_le_normalizer (V₁ := V₁) (Vp := V) hBH
  have hUle : Nat.card ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))) ≤
      ((B ⊓ pCoreOf 2 (H₁ ⊔ lOne L V₁)).relIndex B) ^ 2 *
        Nat.card (fixV (autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))))) := by
    have c2 := card_fixV_autOn_eq hUT hn'
    have c3 := A.hF_F4.toHypF91.relIndex_tilde_fixV hBH
    have hmul := Subgroup.relIndex_mul_card (tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)) ⊓
      Subgroup.centralizer (tildeOf V₁ B : Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)))
      (tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))
    rw [inf_eq_left.mpr inf_le_left] at hmul
    rw [c2, ← hmul, c3]
    exact Nat.mul_le_mul_right _ hr

  set Bs := autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))) with hBsdef
  set K := Bs.subgroupOf (A.Cs_F4 ⊔ A.Ls_F4) with hK
  set A' := K.map θ with hA'
  have hKC : ∀ k ∈ K, ((k : ↥(A.Cs_F4 ⊔ A.Ls_F4)) : MulAut _) ∈ A.Cs_F4 := fun k hk => hBsC hk
  have hcardA' : Nat.card A' = (B ⊓ pCoreOf 2 (H₁ ⊔ lOne L V₁)).relIndex B := by
    rw [hA', card_map_of_ker θ fun k hk h1 => Subtype.ext (hθinj _ (hKC k hk) h1), ← hq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hBsC.trans le_sup_left)).toEquiv
  have hfix := hcard Bs hBsC

  set X := (A.psi1_F4 θ).range with hX
  have hA'X : A' ≤ X := by
    rintro _ ⟨k, hk, rfl⟩
    have hk' : (k : MulAut _) ∈ (B.subgroupOf (H₁ ⊔ lOne L V₁)).map A.rho_F4 := hBs ▸ hk
    obtain ⟨⟨b, hbH⟩, hb, hbk⟩ := hk'
    have hb' : b ∈ B := hb
    refine ⟨⟨b, hBH₁ hb'⟩, ?_⟩
    rw [psi1_apply_F4]
    congr 1
    exact Subtype.ext hbk
  have hBsel := isElemAbelian2_autOn hUT (isElemAbelian_secImg hBel) hn'
  have hA'el : IsElemAbelian2 A' := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨k₁, hk₁, rfl⟩ _ ⟨k₂, hk₂, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hBsel.1 _ hk₁ _ hk₂)
    · rintro _ ⟨k, hk, rfl⟩
      rw [← map_pow]
      have : k ^ 2 = 1 := Subtype.ext (hBsel.2 _ hk)
      rw [this, map_one]
  have hA'ne : A' ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hcardA'
    omega

  have hO2 := A.pCoreOf_eq_bot_F4 hθL hθinj

  have hmp := Hyp1223.minParabolic_of_isHStar_F4 h331 A.cx.hyp.hyp A.hstar
  have hsqtk := isSQTKSub_of_inH A.cx.hyp.hyp.qtke A.cx.hyp.hyp.simple
    A.cx.hyp.hyp.nonabelian A.hstar.1
  have hnotFF : ¬ IsStrongFFModule X := by
    by_cases hker : (A.psi1_F4 θ).rangeRestrict.ker ≤
        (H₁ ⊓ Subgroup.normalizer (L : Set G)).subgroupOf H₁
    · exact hB _ hsqV X _ _
        ⟨↥H₁, inferInstance, inferInstance, hsqtk.2, hsqtk.1, _,
          (A.psi1_F4 θ).rangeRestrict_surjective⟩
        (MinParabolic.map_of_surjective hmp.subgroupOf (A.psi1_F4 θ).rangeRestrict_surjective hker)
        hO2
    · exfalso
      rw [MonoidHom.ker_rangeRestrict] at hker
      obtain ⟨k, hk, hkM⟩ := IsConcreteLE.not_le_iff_exists.1 hker
      have hkM' : (k : G) ∉ Subgroup.normalizer (L : Set G) := fun h => hkM ⟨k.2, h⟩

      set K' := (A.psi1_F4 θ).ker.map H₁.subtype with hK'
      have hK'H : K' ≤ H₁ := Subgroup.map_subtype_le _
      have hTK' : T ≤ Subgroup.normalizer (K' : Set G) := by
        refine LinearS3.le_normalizer_of_conj_mem fun t ht x hx => ?_
        obtain ⟨y, hy, rfl⟩ := hx
        have htH : t ∈ H₁ := A.T_le_F4 ht
        refine ⟨⟨t, htH⟩ * y * ⟨t, htH⟩⁻¹, ?_, rfl⟩
        exact (MonoidHom.normal_ker _).conj_mem y hy _
      obtain ⟨S, hS⟩ := exists_sylow_coe_eq A.cx.hyp.hyp.sylow
      have hY : K' ⊔ T = H₁ := by
        refine A.hstar.2.2 _ ?_ (sup_le hK'H A.T_le_F4) fun hle => hkM' (hle ?_)
        · have h1 := inH_of_le S (Y := K' ⊔ T) (H := H₁) (by rw [hS]; exact le_sup_right)
            (sup_le hK'H A.T_le_F4) (by rw [hS]; exact A.hstar.1)
          rwa [hS] at h1
        · exact Subgroup.mem_sup_left ⟨k, hk, rfl⟩

      have hXp : IsPGroup 2 ↥X := by
        rintro ⟨_, ⟨h, rfl⟩⟩
        have hh : (h : G) ∈ ((K' ⊔ T : Subgroup G) : Set G) := by rw [hY]; exact h.2
        rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTK'] at hh
        obtain ⟨a, ha, t, ht, hat⟩ := hh
        obtain ⟨a', ha', rfl⟩ := ha
        have htH : t ∈ H₁ := A.T_le_F4 ht
        have e : h = a' * ⟨t, htH⟩ := Subtype.ext hat.symm
        obtain ⟨j, hj⟩ := A.cx.hyp.hyp.sylow.1 ⟨t, ht⟩
        refine ⟨j, Subtype.ext ?_⟩
        have hj' : (⟨t, htH⟩ : ↥H₁) ^ 2 ^ j = 1 :=
          Subtype.ext (by simpa using congrArg Subtype.val hj)
        simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
        rw [e, map_mul, MonoidHom.mem_ker.1 ha', one_mul, ← map_pow, hj', map_one]

      have htop : (⊤ : Subgroup ↥X) ≤ pCoreOf 2 (⊤ : Subgroup ↥X) :=
        LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer
          (hXp.of_equiv Subgroup.topEquiv.symm)
      rw [hO2, le_bot_iff] at htop
      apply hA'ne
      rw [eq_bot_iff]
      intro a ha
      have h1 : (⟨a, hA'X ha⟩ : ↥X) ∈ (⊤ : Subgroup ↥X) := Subgroup.mem_top _
      rw [htop, Subgroup.mem_bot] at h1
      exact (Subgroup.mem_bot).2 (congrArg Subtype.val h1)

  have hFF : (B ⊓ pCoreOf 2 (H₁ ⊔ lOne L V₁)).relIndex B * Nat.card (fixV A') ≤ 2 ^ m := by
    by_contra hlt
    push Not at hlt
    apply hnotFF
    refine ⟨A', hA'X, hA'ne, hA'el, ?_⟩
    rw [hV, hcardA']
    exact hlt

  set q := (B ⊓ pCoreOf 2 (H₁ ⊔ lOne L V₁)).relIndex B with hqdef
  set F := Nat.card (fixV A') with hF
  have hFpos : 0 < F ^ (n - 1) := pow_pos Nat.card_pos _
  have h1 : (q * F) ^ (n - 1) ≤ q ^ 2 * F ^ (n - 1) := by
    calc (q * F) ^ (n - 1) ≤ (2 ^ m) ^ (n - 1) := Nat.pow_le_pow_left hFF _
      _ = Nat.card ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))) := hcardW.symm
      _ ≤ q ^ 2 * Nat.card (fixV Bs) := hUle
      _ = q ^ 2 * F ^ (n - 1) := by rw [hfix]
  rw [mul_pow] at h1
  have h2 : q ^ (n - 1) ≤ q ^ 2 := Nat.le_of_mul_le_mul_right h1 hFpos
  have h3 : q ^ 3 ≤ q ^ (n - 1) := Nat.pow_le_pow_right (by omega) hd
  have h4 : q ^ 2 * 2 ≤ q ^ 2 * q := Nat.mul_le_mul_left _ hq2
  have h5 : q ^ 2 * q = q ^ 3 := by ring
  have h6 : 0 < q ^ 2 := pow_pos (by omega) _
  omega

end Am_F4

end L1295A

theorem case1295Amalgam_of_F4 (h1222 : Stmt12_2_2_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h331 : Stmt3_3_1_F4) (hB : B69One) : Case1295Amalgam_F4 := by
  intro G _ _ T L V n hcx V₁ H₁ hV₁ hU hH₁ hH₁V₁ hH₁L₁ hcomm
  exact (L1295A.Am_F4.mk h1222 h37 h38 h39 hcx hV₁ hU hH₁ hH₁V₁ hH₁L₁ hcomm).false_of_F4 h331 hB

end CFSG.Quasithin.H13
