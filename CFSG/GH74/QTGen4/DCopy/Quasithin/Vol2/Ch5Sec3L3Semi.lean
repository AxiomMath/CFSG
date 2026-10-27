module

public import CFSG.Quasithin.Vol2.Ch5Sec3L3Semi
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3L3Local
import CFSG.Quasithin.Vol2.Ch3Sec1Thm311

public section

namespace CFSG.Quasithin.H13.Sec53L3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F1
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.L3 CFSG.Quasithin.SL2Semilinear
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.QuasithinUnique.Fin257.L3

section Coordinates

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D L₂ : Subgroup G} {n f : ℕ}

theorem exists_v1Coords_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hty : IsOfLieType52 M L H B D T .PSL 3 f) (hf : 2 ≤ f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ f ∧
      Nonempty (V1Coords (sec53G1 M L H B) (sec53G1 M L H B ⊓ sec53G2 M L H D) L (pCoreOf 2 L)
        (pCoreOf 2 (oTwoUpper H)) (sec53ZS T L) F) := by
  obtain ⟨F, hFf, hFfin, hFchar, hFcard, ⟨Mo⟩⟩ := exists_l3Model hty hf
  refine ⟨F, hFf, hFfin, hFchar, hFcard, ?_⟩
  have hRc : Nonempty (RadCoords Mo.R₁ Mo.R₂) := by
    rcases Mo.radicals with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact ⟨radCoords_V1⟩
    · rw [h1, h2]; exact ⟨radCoords_V2⟩
  obtain ⟨Rc⟩ := hRc
  set N := Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)) with hN
  have hRN : Mo.R₁ ≤ N := Subgroup.le_normalizer
  have hR₂N : Mo.R₂ ≤ N :=
    Mo.data.borel.le₂.trans (Subgroup.le_normalizer.trans Mo.data.borel.lt₁.le)
  have hb := Mo.b₁_injective

  have hbφ : ∀ (g : G) (hg : g ∈ sec53G1 M L H B), Mo.b₁ (isoφ1 Mo.iso ⟨g, hg⟩) = g := by
    intro g hg
    show (((isoφ1 Mo.iso).symm (isoφ1 Mo.iso ⟨g, hg⟩) : ↥(sec53G1 M L H B)) : G) = g
    rw [MulEquiv.symm_apply_apply]
  have hV₁ := Mo.subImg_R₁ hyp
  have hV₂ := Mo.subImg_R₂ hyp hty
  have hZ := Mo.subImg_Z_F4 h527 hyp
  have hG₁L := G1_le_normalizer hyp
  have hV₂L : pCoreOf 2 (oTwoUpper H) ≤ L :=
    (le_sup_right.trans (sup_sec53_F4 h527 hyp hty hf).le).trans (inf_le_right : sec53S T L ≤ L)
  let ι : F × F → G := fun p => Mo.b₁ ⟨Rc.co p, hRN (Rc.co_mem p)⟩
  have hιV : ∀ p, ι p ∈ pCoreOf 2 L := fun p => by
    rw [← hV₁]
    exact mem_subImg_of_mem Mo.b₁ _ (Rc.co_mem p)
  have hιG₁ : ∀ p, ι p ∈ sec53G1 M L H B := fun p => ((isoφ1 Mo.iso).symm _).2

  have hconj : ∀ (m x : projectiveSL 3 F) (hm : m ∈ N) (hx : x ∈ N),
      Mo.b₁ ⟨m, hm⟩ * Mo.b₁ ⟨x, hx⟩ * (Mo.b₁ ⟨m, hm⟩)⁻¹ =
        Mo.b₁ ⟨m * x * m⁻¹, N.mul_mem (N.mul_mem hm hx) (N.inv_mem hm)⟩ := by
    intro m x hm hx
    rw [← map_mul, ← map_inv, ← map_mul]
    rfl
  have hιeq : ∀ (p : F × F) (x : projectiveSL 3 F) (hx : x ∈ N), x = Rc.co p →
      Mo.b₁ ⟨x, hx⟩ = ι p := by
    rintro p _ hx rfl
    rfl
  refine ⟨{
    ι := ι
    mem := hιV
    add := fun p q => by
      show Mo.b₁ _ = Mo.b₁ _ * Mo.b₁ _
      rw [← map_mul]
      congr 1
      exact Subtype.ext (Rc.co_add p q)
    inj := fun p q h => Rc.co_inj (congrArg Subtype.val (hb h))
    surj := fun v hv => by
      rw [← hV₁] at hv
      obtain ⟨x, hx, hxR, rfl⟩ := mem_subImg.mp hv
      obtain ⟨p, rfl⟩ := Rc.co_surj x hxR
      exact ⟨p, rfl⟩
    center := fun v => by
      rw [← hZ, mem_subImg]
      constructor
      · rintro ⟨x, hx, hxZ, rfl⟩
        obtain ⟨c, rfl⟩ := (Rc.center x).mp hxZ
        exact ⟨c, rfl⟩
      · rintro ⟨c, rfl⟩
        exact ⟨_, hRN (Rc.co_mem (0, c)), (Rc.center _).mpr ⟨c, rfl⟩, rfl⟩
    lin := fun g hg => by
      set m : projectiveSL 3 F := ((isoφ1 Mo.iso ⟨g, hg⟩ : ↥N) : projectiveSL 3 F) with hm
      have hmN : m ∈ N := (isoφ1 Mo.iso ⟨g, hg⟩).2
      obtain ⟨α, β, γ, δ, hlin⟩ := Rc.lin m hmN
      refine ⟨α, β, γ, δ, fun u v => ?_⟩
      have hg' : Mo.b₁ ⟨m, hmN⟩ = g := hbφ g hg
      rw [← hg']
      show Mo.b₁ ⟨m, hmN⟩ * Mo.b₁ ⟨Rc.co (u, v), _⟩ * (Mo.b₁ ⟨m, hmN⟩)⁻¹ = ι _
      rw [hconj]
      exact hιeq _ _ _ (hlin u v)
    xe := fun β => Mo.b₁ ⟨Rc.s * Rc.y β * Rc.s⁻¹,
      N.mul_mem (N.mul_mem Rc.s_mem (hR₂N (Rc.y_mem β))) (N.inv_mem Rc.s_mem)⟩
    xe_mem := fun β => by
      rw [← hconj Rc.s (Rc.y β) Rc.s_mem (hR₂N (Rc.y_mem β))]
      have hyV : Mo.b₁ ⟨Rc.y β, hR₂N (Rc.y_mem β)⟩ ∈ pCoreOf 2 (oTwoUpper H) := by
        rw [← hV₂]
        exact mem_subImg_of_mem Mo.b₁ _ (Rc.y_mem β)
      have hsG : Mo.b₁ ⟨Rc.s, Rc.s_mem⟩ ∈ sec53G1 M L H B := ((isoφ1 Mo.iso).symm _).2
      exact (Subgroup.mem_normalizer_iff.mp (hG₁L hsG) _).mp (hV₂L hyV)
    xe_act := fun β p => by
      show Mo.b₁ _ * Mo.b₁ ⟨Rc.co p, _⟩ * (Mo.b₁ _)⁻¹ = ι _
      rw [hconj]
      refine hιeq _ _ _ ?_
      obtain ⟨u, v⟩ := p
      have h1 : Rc.s⁻¹ * Rc.co (u, v) * Rc.s = Rc.co (v, u) := by
        have := Rc.s_swap v u
        rw [← this]
        group
      calc Rc.s * Rc.y β * Rc.s⁻¹ * Rc.co (u, v) * (Rc.s * Rc.y β * Rc.s⁻¹)⁻¹ =
            Rc.s * (Rc.y β * (Rc.s⁻¹ * Rc.co (u, v) * Rc.s) * (Rc.y β)⁻¹) * Rc.s⁻¹ := by group
        _ = Rc.s * Rc.co (tvY β (v, u)) * Rc.s⁻¹ := by rw [h1, Rc.y_act]
        _ = Rc.co (tvX β (u, v)) := by
          rw [tvY_apply, tvX_apply, Rc.s_swap]
    ye := fun β => Mo.b₁ ⟨Rc.y β, hR₂N (Rc.y_mem β)⟩
    ye_mem := fun β => by
      rw [← hV₂]
      exact mem_subImg_of_mem Mo.b₁ _ (Rc.y_mem β)
    ye_act := fun β p => by
      show Mo.b₁ _ * Mo.b₁ ⟨Rc.co p, _⟩ * (Mo.b₁ _)⁻¹ = ι _
      rw [hconj]
      exact hιeq _ _ _ (Rc.y_act β p)
    tor := fun t => by
      obtain ⟨d, hdU, hd⟩ := Rc.tor t
      rw [← normalizer_inf_normalizer Mo.data] at hdU
      obtain ⟨hd1, hd2⟩ := Subgroup.mem_inf.mp hdU
      have hbG₁ : Mo.b₁ ⟨d, hd1⟩ ∈ sec53G1 M L H B := ((isoφ1 Mo.iso).symm _).2
      have hbd : isoφ1 Mo.iso ⟨Mo.b₁ ⟨d, hd1⟩, hbG₁⟩ = ⟨d, hd1⟩ :=
        (isoφ1 Mo.iso).apply_symm_apply ⟨d, hd1⟩
      have hbG₂ : Mo.b₁ ⟨d, hd1⟩ ∈ sec53G2 M L H D :=
        Mo.mem_G2_of_mem_normalizer ⟨_, hbG₁⟩ (by rw [hbd]; exact hd2)
      refine ⟨Mo.b₁ ⟨d, hd1⟩, Subgroup.mem_inf.mpr ⟨hbG₁, hbG₂⟩, fun u v => ?_⟩
      show Mo.b₁ ⟨d, hd1⟩ * Mo.b₁ ⟨Rc.co (u, v), _⟩ * (Mo.b₁ ⟨d, hd1⟩)⁻¹ = ι _
      rw [hconj]
      exact hιeq _ _ _ (hd u v) }⟩

end Coordinates

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D L₂ : Subgroup G} {n f : ℕ}

theorem l3facts_one_F4 (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hty : IsOfLieType52 M L H B D T .PSL 3 f) (hf : 2 ≤ f) :
    T ⊓ Subgroup.centralizer (sec53ZS T L : Set G) = sec53S T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · intro t ht
    obtain ⟨htT, htc⟩ := Subgroup.mem_inf.mp ht
    have h := hyp.toHyp5_1_8.toHyp5_0_1
    have htL : t ∈ Subgroup.normalizer (L : Set G) := h.normal (h.T_le htT)
    have htV : t ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L htL
    obtain ⟨F, _, _, _, -, ⟨C⟩⟩ := exists_v1Coords_F4 h527 hyp hty hf
    have hLG : L ≤ sec53G1 M L H B := le_sup_left.trans le_sup_left
    have hsup := sup_sec53_F4 h527 hyp hty hf
    have hV₂S : pCoreOf 2 (oTwoUpper H) ≤ sec53S T L := le_sup_right.trans hsup.le
    have hV₁S : pCoreOf 2 L ≤ sec53S T L := le_sup_left.trans hsup.le
    have hV₂L : pCoreOf 2 (oTwoUpper H) ≤ L := hV₂S.trans inf_le_right
    obtain ⟨τ, σ, hτ, hσ⟩ := C.exists_semilinear hLG hV₂L htL htV

    have hfix : ∀ c : F, τ (0, c) = (0, c) := fun c => C.inj (by
      rw [hτ]
      have hz : C.ι (0, c) ∈ sec53ZS T L := (C.center _).mpr ⟨c, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp htc _ hz
      rw [← this]
      group)

    have hσ1 : ∀ c : F, σ c = c := fun c => by
      have h1 := hσ c (0, 1)
      have e : c • ((0 : F), (1 : F)) = (0, c) := by ext <;> simp
      rw [e, hfix, hfix] at h1
      have := congrArg Prod.snd h1
      simp at this
      exact this.symm
    set ν := (τ (1, 0)).1 with hν
    set β := (τ (1, 0)).2 with hβ
    have hform : ∀ q : F × F, τ q = (q.1 * ν, q.1 * β + q.2) := by
      intro q
      have e : q = q.1 • ((1 : F), (0 : F)) + q.2 • ((0 : F), (1 : F)) := by ext <;> simp
      rw [e, map_add, hσ, hσ, hσ1, hσ1, hfix]
      ext <;> simp [hν, hβ]

    obtain ⟨k, hk⟩ := (hyp.toHyp5_1_8.toHyp5_0_1.sylow.1) ⟨t, htT⟩
    have hk' : t ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hiter : ∀ (m : ℕ) (p : F × F), C.ι ((⇑τ)^[m] p) = t ^ m * C.ι p * (t ^ m)⁻¹ := by
      intro m
      induction m with
      | zero => intro p; simp
      | succ m ih =>
        intro p
        rw [Function.iterate_succ_apply', hτ, ih, pow_succ']
        group
    have hfirst : ∀ m : ℕ, ((⇑τ)^[m] ((1 : F), (0 : F))).1 = ν ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [Function.iterate_succ_apply', hform, ih, pow_succ]
    have hν1 : ν = 1 := by
      have h1 : (⇑τ)^[2 ^ k] ((1 : F), (0 : F)) = (1, 0) := C.inj (by
        rw [hiter, hk', inv_one, one_mul, mul_one])
      have h2 := hfirst (2 ^ k)
      rw [h1] at h2
      have h3 : (ν - 1) ^ 2 ^ k = 0 := by
        rw [sub_pow_char_pow, ← h2, one_pow, sub_self]
      have := pow_eq_zero_iff (n := 2 ^ k) (by positivity) |>.mp h3
      linear_combination this

    have hτY : ∀ p, τ p = tvY β p := fun p => by
      rw [hform, hν1, tvY_apply]
      ext <;> simp [mul_comm, add_comm]
    set y := C.ye β with hy
    have hyV₂ : y ∈ pCoreOf 2 (oTwoUpper H) := C.ye_mem β
    have hxc : y⁻¹ * t ∈ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      obtain ⟨p, rfl⟩ := C.surj v hv
      have e1 : t * C.ι p * t⁻¹ = y * C.ι p * y⁻¹ := by rw [← hτ, hτY, C.ye_act]
      calc C.ι p * (y⁻¹ * t) = y⁻¹ * (y * C.ι p * y⁻¹) * t := by group
        _ = y⁻¹ * (t * C.ι p * t⁻¹) * t := by rw [e1]
        _ = y⁻¹ * t * C.ι p := by group
    have hpar : IsSec53Param .PSL 3 f := ⟨hf, Or.inl ⟨rfl, rfl⟩⟩
    obtain ⟨-, ⟨hCT, hO2, -, -⟩, -, -⟩ := h531 G T M L V H B D L₂ n .PSL 3 f hyp hty hpar
    have hxM : y⁻¹ * t ∈ sec53M1 L :=
      (sec53M1 L).mul_mem ((sec53M1 L).inv_mem (Subgroup.le_normalizer (hV₂L hyV₂))) htL
    have hxV : y⁻¹ * t ∈ pCoreOf 2 L := by
      rw [← hO2]
      refine hCT (Subgroup.mem_inf.mpr ⟨hxM, ?_⟩)
      rw [hO2]
      exact hxc
    have : t = y * (y⁻¹ * t) := by group
    rw [this]
    exact (sec53S T L).mul_mem (hV₂S hyV₂) (hV₁S hxV)
  · intro s hs
    refine Subgroup.mem_inf.mpr ⟨(inf_le_left : sec53S T L ≤ T) hs, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzc : z ∈ Subgroup.centralizer (sec53S T L : Set G) :=
      (inf_le_right : sec53ZS T L ≤ Subgroup.centralizer (sec53S T L : Set G)) hz
    exact (Subgroup.mem_centralizer_iff.mp hzc s hs).symm

variable {F : Type} [Field F]

theorem l3facts_six_of_three_le_F4 (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f)
    (hf : 2 ≤ f) (hf3 : 3 ≤ f) :
    ∀ z ∈ sec53ZS T L, z ∈ centerOf T → z ≠ 1 →
      pCoreOf 2 (sec53M1 L ⊓ Subgroup.centralizer ({z} : Set G)) = sec53S T L ∧
        pCoreOf 2 (sec53M2 H ⊓ Subgroup.centralizer ({z} : Set G)) = sec53S T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro z hz hzT hz1
  have h := hyp.toHyp5_1_8.toHyp5_0_1
  have hpar : IsSec53Param .PSL 3 f := ⟨hf, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨-, -, ⟨hN, -, -⟩, -, -⟩ := h531 G T M L V H B D L₂ n .PSL 3 f hyp hty hpar
  obtain ⟨h5a, h5b⟩ := l3facts_five_F4 h527 h531 hyp hty hf z hz hz1
  set X := sec53M12 L H ⊓ Subgroup.centralizer ({z} : Set G) with hX
  have hX1 : sec53M1 L ⊓ Subgroup.centralizer ({z} : Set G) = X :=
    le_antisymm (le_inf h5a inf_le_right) (inf_le_inf_right _ inf_le_left)
  have hX2 : sec53M2 H ⊓ Subgroup.centralizer ({z} : Set G) = X :=
    le_antisymm (le_inf h5b inf_le_right) (inf_le_inf_right _ inf_le_right)
  rw [hX1, hX2, and_self]
  have hzS : z ∈ sec53S T L := (inf_le_left : centerOf (sec53S T L) ≤ sec53S T L) hz

  have hTN : T ≤ Subgroup.normalizer (sec53S T L : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have htL : t ∈ Subgroup.normalizer (L : Set G) := h.normal (h.T_le ht)
    constructor
    · rintro ⟨hyT, hyL⟩
      exact ⟨T.mul_mem (T.mul_mem ht hyT) (T.inv_mem ht),
        (Subgroup.mem_normalizer_iff.mp htL y).mp hyL⟩
    · rintro ⟨hyT, hyL⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp htL y).mpr hyL⟩
      have := T.mul_mem (T.mul_mem (T.inv_mem ht) hyT) ht
      simpa [mul_assoc] using this
  have hTX : T ≤ X := by
    intro t ht
    refine Subgroup.mem_inf.mpr ⟨by rw [← hN]; exact hTN ht, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp ((inf_le_right : centerOf T ≤
      Subgroup.centralizer (T : Set G)) hzT) t ht)
  apply le_antisymm
  · intro x hx
    have hxT : x ∈ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf
      (isSylowTwoOf_of_isSylowTwo h.sylow hTX) hx
    have hxL : x ∈ Subgroup.normalizer (L : Set G) := h.normal (h.T_le hxT)
    have hxV : x ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hxL
    obtain ⟨F, _, _, _, hFcard, ⟨C⟩⟩ := exists_v1Coords_F4 h527 hyp hty hf
    have hLG : L ≤ sec53G1 M L H B := le_sup_left.trans le_sup_left
    have hsup := sup_sec53_F4 h527 hyp hty hf
    have hV₂S : pCoreOf 2 (oTwoUpper H) ≤ sec53S T L := le_sup_right.trans hsup.le
    have hV₂L : pCoreOf 2 (oTwoUpper H) ≤ L := hV₂S.trans inf_le_right
    obtain ⟨τ, σ, hτ, hσ⟩ := C.exists_semilinear hLG hV₂L hxL hxV

    have hxZ : ∀ y ∈ sec53ZS T L, x * y * x⁻¹ ∈ sec53ZS T L := fun y hy =>
      conj_mem_centerOf (hTN hxT) hy
    have hZ : (τ (0, 1)).1 = 0 := by
      have h1 : C.ι (τ (0, 1)) ∈ sec53ZS T L := by
        rw [hτ]
        exact hxZ _ ((C.center _).mpr ⟨1, rfl⟩)
      obtain ⟨c, hc⟩ := (C.center _).mp h1
      rw [C.inj hc]

    obtain ⟨c₀, rfl⟩ := (C.center z).mp hz
    have hc₀ : c₀ ≠ 0 := by
      rintro rfl
      apply hz1
      have := C.add 0 0
      rw [add_zero] at this
      have h0 : C.ι ((0 : F), (0 : F)) = C.ι 0 := rfl
      rw [h0]
      exact (mul_eq_left.mp this.symm)

    have hPX : ∀ g ∈ X, ∀ y ∈ pCoreOf 2 X, g * y * g⁻¹ ∈ pCoreOf 2 X := fun g hg y hy =>
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hg) y).mp hy
    have hP2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X

    have hcube : ∀ t : F, σ (t ^ 3) = t ^ 3 := by
      intro t
      by_cases ht0 : t = 0
      · rw [ht0]; simp
      obtain ⟨g, hgB, hg⟩ := C.tor (Units.mk0 t ht0)
      have hgM : g ∈ sec53M12 L H := inf_le_sec53M12 hyp hgB
      have hgC : g ∈ Subgroup.centralizer ({C.ι (0, c₀)} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h3 := hg 0 c₀
        rw [mul_zero] at h3
        calc g * C.ι (0, c₀) = g * C.ι (0, c₀) * g⁻¹ * g := by group
          _ = C.ι (0, c₀) * g := by rw [h3]
      have hgX : g ∈ X := Subgroup.mem_inf.mpr ⟨hgM, hgC⟩
      have hgV : g ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
        CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
          (G1_le_normalizer hyp (Subgroup.mem_inf.mp hgB).1)
      have hcomm : x * g * x⁻¹ * g⁻¹ ∈ pCoreOf 2 X := by
        have := hPX g hgX x⁻¹ (Subgroup.inv_mem _ hx)
        have := (pCoreOf 2 X).mul_mem hx this
        simpa [mul_assoc] using this
      obtain ⟨k, hk⟩ := hP2 ⟨_, hcomm⟩
      have hk' : (x * g * x⁻¹ * g⁻¹) ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have := C.sigma_fix_of_diag hxV hgV hτ hσ hZ (pow_ne_zero 3 ht0) hg hk'
      simpa using this
    have hF4 : 4 < Nat.card F := by
      rw [hFcard]
      calc 4 < 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
    have hσid : ∀ c, σ c = c := eq_of_fix_cube hF4 σ hcube

    have hxz : τ (0, c₀) = (0, c₀) := C.inj (by
      rw [hτ]
      have h3 := Subgroup.mem_centralizer_singleton_iff.mp
        (Subgroup.mem_inf.mp (CFSG.LieType.BorelTits.pCoreOf_le 2 X hx)).2
      calc x * C.ι (0, c₀) * x⁻¹ = C.ι (0, c₀) * x * x⁻¹ := by rw [h3]
        _ = C.ι (0, c₀) := by group)
    have hfixZ : ∀ c : F, τ (0, c) = (0, c) := by
      intro c
      have e : ((0 : F), c) = (c * c₀⁻¹) • ((0 : F), c₀) := by
        ext
        · simp
        · show c = c * c₀⁻¹ * c₀
          field_simp
      rw [e, hσ, hσid, hxz]
    have hxC : x ∈ Subgroup.centralizer (sec53ZS T L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨c, rfl⟩ := (C.center y).mp hy
      have h3 : x * C.ι (0, c) * x⁻¹ = C.ι (0, c) := by rw [← hτ, hfixZ]
      calc C.ι (0, c) * x = x * C.ι (0, c) * x⁻¹ * x := by rw [h3]
        _ = x * C.ι (0, c) := by group
    rw [← l3facts_one_F4 h527 h531 hyp hty hf]
    exact Subgroup.mem_inf.mpr ⟨hxT, hxC⟩
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (le_inf (by rw [← hN]; exact Subgroup.le_normalizer) ?_)
      (inf_le_left.trans hN.symm.le) (h.sylow.1.to_le (inf_le_left : sec53S T L ≤ T))
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp ((inf_le_right : centerOf (sec53S T L) ≤
      Subgroup.centralizer (sec53S T L : Set G)) hz) s hs)

end CFSG.Quasithin.H13.Sec53L3
