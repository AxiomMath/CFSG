module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Defs
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Gen
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Frob

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits

section Base

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem Node10.isElemAbelian_V (h : Node10 d z₀) : IsElemAbelian 2 d.s56V := h.2.1

theorem Node10.card_V (h : Node10 d z₀) : Nat.card d.s56V = 2 ^ 10 := h.2.2.1

theorem Node10.comm_V (h : Node10 d z₀) {a b : G} (ha : a ∈ d.s56V) (hb : b ∈ d.s56V) :
    a * b = b * a := by
  have := h.isElemAbelian_V.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val this

theorem Node10.sq_V (h : Node10 d z₀) {a : G} (ha : a ∈ d.s56V) : a * a = 1 := by
  have := h.isElemAbelian_V.2 a ha
  simpa [pow_two] using this

theorem Node05.card_Q (h : Node05 d z₀) : Nat.card d.s56Q = 2 ^ 14 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h10, -, -⟩ := h
  exact h10

theorem M_le_Hg (h49 : d.Thm49Statement) (hd : d.Hyp) : d.M ≤ Hg d :=
  hd.s56_M_le_normalizer_V h49

theorem mem_Hg_iff {g : G} : g ∈ Hg d ↔ g ∈ normalizer (d.s56V : Set G) := Iff.rfl

theorem star_eq (g : G) : star d g = actFun d.s56V g := rfl

theorem img_eq (K : Subgroup G) : img d K = imgIn d.s56V K := rfl

theorem Cv_eq : Cv d = centralizer (d.s56V : Set G) := rfl

theorem V_le_Q : d.s56V ≤ d.s56Q := inf_le_left

theorem V_le_Q2 : d.s56V ≤ d.s56Q2 := inf_le_right

theorem V_le_M : d.s56V ≤ d.M := d.s56_V_le_M

theorem Q_le_Q0 (hd : d.Hyp) : d.s56Q ≤ d.s56Q0 := hd.s56_Q_le_Q0

theorem Q0_le_M (h49 : d.Thm49Statement) (hd : d.Hyp) : d.s56Q0 ≤ d.M := hd.s56_Q0_le_M h49

theorem Q_le_M (h49 : d.Thm49Statement) (hd : d.Hyp) : d.s56Q ≤ d.M :=
  (Q_le_Q0 hd).trans (Q0_le_M h49 hd)

theorem Xg_le_M (hd : d.Hyp) : Xg d ≤ d.M := hd.s56_X_le_M

theorem V_le_Cv (h10 : Node10 d z₀) : d.s56V ≤ Cv d :=
  fun v hv => mem_centralizer_iff.2 fun w hw => h10.comm_V hw hv

theorem star_V (h10 : Node10 d z₀) {v : G} (hv : v ∈ d.s56V) : star d v = 1 :=
  (actFun_eq_one_iff d.s56V (le_normalizer hv)).2 (V_le_Cv h10 hv)

theorem Q_comm_mem_V (h49 : d.Thm49Statement) (hd : d.Hyp) {q q' : G} (hq : q ∈ d.s56Q)
    (hq' : q' ∈ d.s56Q) : q * q' * q⁻¹ * q'⁻¹ ∈ d.s56V :=
  mem_inf.2 ⟨mul_mem (mul_mem (mul_mem hq hq') (inv_mem hq)) (inv_mem hq'),
    hd.s56_Q0_comm_mem_Q2 h49 (Q_le_Q0 hd hq) (Q_le_Q0 hd hq')⟩

theorem Q_sq_mem_V (h49 : d.Thm49Statement) (hd : d.Hyp) {q : G} (hq : q ∈ d.s56Q) :
    q * q ∈ d.s56V := by
  refine mem_inf.2 ⟨mul_mem hq hq, ?_⟩
  obtain ⟨hqM, hqE⟩ := (hd.s56_mem_Q0_iff h49).1 (Q_le_Q0 hd hq)
  refine (Data.s56_mem_Q2_iff).2 ⟨mul_mem hqM hqM, fun e he => ?_⟩
  have hw := hqE e he
  set w := q * e * q⁻¹ * e⁻¹ with hwdef
  have hwE : w ∈ d.E := hd.s56_zpowers_le_E hw
  have hqw : q * w * q⁻¹ = w := by
    rw [hd.s56_M_comm_zpowers hqM hw]
    group
  have hww : w * w = 1 := hd.s56_zpowers_sq hw
  have hwe : w * e = e * w := hd.s56_E_comm hwE he
  have h1 : q * e * q⁻¹ = w * e := by rw [hwdef]; group
  have h2 : q * (q * e * q⁻¹) * q⁻¹ = e := by
    rw [h1]
    calc q * (w * e) * q⁻¹ = (q * w * q⁻¹) * (q * e * q⁻¹) := by group
      _ = w * (w * e) := by rw [hqw, h1]
      _ = (w * w) * e := by group
      _ = e := by rw [hww, one_mul]
  have h3 : (q * q) * e * (q * q)⁻¹ = e := by
    calc (q * q) * e * (q * q)⁻¹ = q * (q * e * q⁻¹) * q⁻¹ := by group
      _ = e := h2
  exact (mul_inv_eq_iff_eq_mul.1 h3).symm

theorem Q_inf_Cv (h49 : d.Thm49Statement) (hd : d.Hyp) (h10 : Node10 d z₀) :
    d.s56Q ⊓ Cv d = d.s56V := by
  refine le_antisymm (fun q hq => ?_) (fun v hv => ⟨V_le_Q hv, V_le_Cv h10 hv⟩)
  obtain ⟨hqQ, hqC⟩ := hq
  refine mem_inf.2 ⟨hqQ, (Data.s56_mem_Q2_iff).2 ⟨Q_le_M h49 hd hqQ, fun e he => ?_⟩⟩
  exact (mem_centralizer_iff.1 hqC e (hd.s56_E_le_V h49 he))

theorem card_img_Q (h49 : d.Thm49Statement) (hd : d.Hyp) (h05 : Node05 d z₀)
    (h10 : Node10 d z₀) : Nat.card (img d d.s56Q) = 2 ^ 4 := by
  have h := card_imgIn_mul_card d.s56V d.s56Q
  have hQN : d.s56Q ≤ normalizer (d.s56V : Set G) := (Q_le_M h49 hd).trans (M_le_Hg h49 hd)
  rw [inf_eq_left.2 hQN, show d.s56Q ⊓ centralizer (d.s56V : Set G) = d.s56V from
    Q_inf_Cv h49 hd h10, h05.card_Q, h10.card_V] at h
  have h2 : Nat.card (imgIn d.s56V d.s56Q) * 2 ^ 10 = 2 ^ 4 * 2 ^ 10 := by
    rw [h]
    norm_num
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h2

theorem isElemAbelian_img_Q (h49 : d.Thm49Statement) (hd : d.Hyp) (h10 : Node10 d z₀) :
    IsElemAbelian 2 (img d d.s56Q) :=
  isElemAbelian_imgIn_of_comm_sq d.s56V
    (fun a ha b hb => V_le_Cv h10 (Q_comm_mem_V h49 hd ha hb))
    (fun a ha => V_le_Cv h10 (by simpa [pow_two] using Q_sq_mem_V h49 hd ha))

theorem exists_V_mul (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) {m : G}
    (hm : m ∈ d.M) : ∃ v ∈ d.s56V, v⁻¹ * m ∈ CMt d := by
  obtain ⟨v, hvV, hv⟩ := hd.s56_V_eps_surj h49 hz (d.s56Eps m) (hd.s56_eps_mem_E hm)
  have h1 := hd.s56_conj_t m
  have h2 := hd.s56_conj_t v
  rw [hv] at h2
  have h3 : (v⁻¹ * m) * d.t * (v⁻¹ * m)⁻¹ = d.t := by
    calc (v⁻¹ * m) * d.t * (v⁻¹ * m)⁻¹ = v⁻¹ * (m * d.t * m⁻¹) * v := by group
      _ = v⁻¹ * (d.t * d.s56Eps m) * v := by rw [h1]
      _ = v⁻¹ * (v * d.t * v⁻¹) * v := by rw [h2]
      _ = d.t := by group
  exact ⟨v, hvV, mem_inf.2 ⟨mul_mem (inv_mem (V_le_M hvV)) hm,
    mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h3)⟩⟩

theorem CMt_le_M : CMt d ≤ d.M := inf_le_left

theorem Q0_le_Hg (h49 : d.Thm49Statement) (hd : d.Hyp) : d.s56Q0 ≤ Hg d :=
  (Q0_le_M h49 hd).trans (M_le_Hg h49 hd)

theorem Xg_le_Hg (h49 : d.Thm49Statement) (hd : d.Hyp) : Xg d ≤ Hg d :=
  (Xg_le_M hd).trans (M_le_Hg h49 hd)

theorem CMt_le_Hg (h49 : d.Thm49Statement) (hd : d.Hyp) : CMt d ≤ Hg d :=
  CMt_le_M.trans (M_le_Hg h49 hd)

theorem img_Q0_eq (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    img d d.s56Q0 = img d (d.s56Q0 ⊓ CMt d) := by
  refine le_antisymm (fun x hx => ?_) (imgIn_mono _ inf_le_left)
  obtain ⟨g, hgQ, hgN, rfl⟩ := (mem_imgIn_iff d.s56V d.s56Q0).1 hx
  obtain ⟨v, hvV, hvc⟩ := exists_V_mul h49 hd hz (Q0_le_M h49 hd hgQ)
  have hvQ0 : v⁻¹ ∈ d.s56Q0 := inv_mem (Q_le_Q0 hd (V_le_Q hvV))
  refine (mem_imgIn_iff d.s56V _).2 ⟨v⁻¹ * g, mem_inf.2 ⟨mul_mem hvQ0 hgQ, hvc⟩,
    mul_mem (inv_mem (le_normalizer hvV)) hgN, ?_⟩
  rw [actFun_mul d.s56V (inv_mem (le_normalizer hvV)) hgN, actFun_inv d.s56V (le_normalizer hvV),
    star_V h10 hvV |> fun h => show actFun d.s56V v = 1 from h, inv_one, one_mul]

theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro h
  rw [mem_inf, mem_inf, hA h, hB h]

theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem pCoreOf_CMt (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) :
    pCoreOf 2 (CMt d) = d.s56Q0 ⊓ CMt d := by
  have hQ0N : d.M ≤ normalizer (d.s56Q0 : Set G) := Data.s56_M_le_normalizer_Q0 d
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  ·
    set O := pCoreOf 2 (CMt d) with hO
    have hOC : O ≤ CMt d := CFSG.LieType.BorelTits.pCoreOf_le 2 _
    have hOM : O ≤ d.M := hOC.trans CMt_le_M
    have hN : O ⊔ d.s56Q0 ≤ pCoreOf 2 d.M := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (sup_le hOM (Q0_le_M h49 hd))
        ?_ ?_
      · intro m hm
        obtain ⟨v, hvV, hvc⟩ := exists_V_mul h49 hd hz hm
        have hc : v⁻¹ * m ∈ normalizer ((O ⊔ d.s56Q0 : Subgroup G) : Set G) :=
          mem_normalizer_sup (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (CMt d) hvc)
            (hQ0N (CMt_le_M hvc))
        have hv : v ∈ normalizer ((O ⊔ d.s56Q0 : Subgroup G) : Set G) :=
          le_normalizer (mem_sup_right (Q_le_Q0 hd (V_le_Q hvV)))
        have := mul_mem hv hc
        simpa using this
      · have h1 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
        have h2 : IsPGroup 2 d.s56Q0 := Data.s56_Q0_isPGroup d
        exact h1.to_sup_of_normal_right' h2 (fun o ho => hQ0N (hOM ho))
    exact le_inf ((le_sup_left.trans hN).trans (by exact le_rfl)) hOC
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      (IsPGroup.to_le (Data.s56_Q0_isPGroup d) inf_le_left)
    intro c hc
    exact mem_normalizer_inf (hQ0N (CMt_le_M hc)) (le_normalizer hc)

theorem Us_eq_img_Q (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    Us d = img d d.s56Q := by
  have h1 : Us d = ⁅img d (d.s56Q0 ⊓ CMt d), img d (Xg d)⁆ := by
    unfold Us
    rw [pCoreOf_CMt h49 hd hz]
  have h2 : img d d.s56Q = ⁅img d d.s56Q0, img d (Xg d)⁆ :=
    imgIn_commutator d.s56V (Q0_le_Hg h49 hd) (Xg_le_Hg h49 hd)
  rw [h1, h2, img_Q0_eq h49 hd hz h10]

theorem t_not_comm_z0 (hd : d.Hyp) (hz : d.S56Z0 z₀) : ¬ d.t * z₀ = z₀ * d.t := by
  intro h
  have h1 := hd.s56_conj_t z₀
  rw [hz.eps] at h1
  have h2 : z₀ * d.t * z₀⁻¹ = d.t := by rw [← h]; group
  rw [h2] at h1
  have h3 : d.z = 1 := by
    have := mul_left_cancel (a := d.t) (b := d.z) (c := 1) (by simpa using h1.symm)
    exact this
  exact hd.s56_z_ne_one h3

theorem t_mem_M : d.t ∈ d.M := d.s56_t_mem_M

theorem t_mem_Hg (h49 : d.Thm49Statement) (hd : d.Hyp) : d.t ∈ Hg d :=
  M_le_Hg h49 hd t_mem_M

theorem x5_mem_Hg (h49 : d.Thm49Statement) (hd : d.Hyp) : d.x₅ ∈ Hg d :=
  M_le_Hg h49 hd hd.s56_x5_mem_M

theorem star_t_ne (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) :
    star d d.t ≠ 1 := by
  intro h
  have := (actFun_eq_one_iff d.s56V (t_mem_Hg h49 hd)).1 h
  exact t_not_comm_z0 hd hz (mem_centralizer_iff.1 this z₀ hz.mem_V).symm

theorem star_t_not_mem_stab (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) :
    star d d.t ∉ MulAction.stabilizer (MulAut ↥d.s56V) (⟨z₀, hz.mem_V⟩ : ↥d.s56V) := by
  intro h
  have h' : actFun d.s56V d.t ⟨z₀, hz.mem_V⟩ = ⟨z₀, hz.mem_V⟩ := h
  exact t_not_comm_z0 hd hz ((actFun_fixes_iff d.s56V (t_mem_Hg h49 hd) _).1 h')

theorem star_t_mul_self (h49 : d.Thm49Statement) (hd : d.Hyp) :
    star d d.t * star d d.t = 1 := by
  rw [star_eq, ← actFun_mul d.s56V (t_mem_Hg h49 hd) (t_mem_Hg h49 hd), hd.t_mul_self, actFun_one]

theorem star_x5_ne_one (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    star d d.x₅ ≠ 1 := by
  intro h
  have hc := (actFun_eq_one_iff d.s56V (x5_mem_Hg h49 hd)).1 h
  have hCQX := hd.s56_CQX_eq h49 hz.mem_Q hz.mem_Q2 hz.eps hz.comm_x hz.dich
  have hVle : d.s56V ≤ zpowers d.z ⊔ zpowers z₀ := by
    rw [← hCQX]
    refine le_inf (V_le_Q) (fun v hv => ?_)
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨n, rfl⟩ := hg
    have hxv : d.x₅ * v = v * d.x₅ := (mem_centralizer_iff.1 hc v hv).symm
    exact (Commute.zpow_left (show Commute d.x₅ v from hxv) n).eq
  have hcard : Nat.card (zpowers d.z ⊔ zpowers z₀ : Subgroup G) ≤ 4 := by
    have := s56_card_sup_zpowers_le (A := zpowers d.z) (y := z₀)
      (fun a ha => by
        obtain ⟨n, rfl⟩ := ha
        exact (Commute.zpow_left (show Commute d.z z₀ from (hz.cen (hd.s56_z_mem_E)).symm) n).eq)
      (hz.sq)
    rw [hd.s56_card_zpowers_z] at this
    exact this
  have h2 := Subgroup.card_le_of_le hVle
  rw [h10.card_V] at h2
  have := h2.trans hcard
  norm_num at this

theorem star_x5_pow_five (h49 : d.Thm49Statement) (hd : d.Hyp) : star d d.x₅ ^ 5 = 1 := by
  rw [star_eq, ← actFun_pow d.s56V (x5_mem_Hg h49 hd)]
  have : d.x₅ ^ 5 = 1 := by rw [← hd.s56_orderOf_x5]; exact pow_orderOf_eq_one _
  rw [this, actFun_one]

theorem IsV1.mem_C {y₁ : G} (hy : IsV1 d z₀ y₁) : y₁ ∈ centralizer ({d.t} : Set G) := hy.2.2.choose

theorem IsV1.conj_x5 (hd : d.Hyp) {y₁ : G} (hy : IsV1 d z₀ y₁) :
    y₁ * d.x₅ * y₁⁻¹ = d.x₅ ^ 3 := by
  obtain ⟨-, -, hyC, hρ⟩ := hy
  obtain ⟨hX1, -, hX3, hX5c, -⟩ := Model.hatX_facts
  have hXD : Model.hatX ∈ titsD := titsH_le_titsD hX1
  have hX3D : Model.hatX ^ 3 ∈ titsD := pow_mem hXD 3
  have h : (d.ρ ⟨y₁, hyC⟩ : Equiv.Perm (Fin 1755)) * Model.hatX =
      Model.hatX ^ 3 * (d.ρ ⟨y₁, hyC⟩ : Equiv.Perm (Fin 1755)) := by
    rcases hρ with h | h
    · rw [h]
      calc Model.parrottV 1 * Model.hatX
          = (Model.parrottV 1 * Model.hatX * (Model.parrottV 1)⁻¹) * Model.parrottV 1 := by group
        _ = Model.hatX ^ 3 * Model.parrottV 1 := by rw [hX3]
    · rw [h]
      calc Model.parrottV 1 * Model.parrottV 5 * Model.hatX
          = Model.parrottV 1 * (Model.parrottV 5 * Model.hatX) := by group
        _ = Model.parrottV 1 * (Model.hatX * Model.parrottV 5) := by rw [hX5c]
        _ = (Model.parrottV 1 * Model.hatX * (Model.parrottV 1)⁻¹) *
            (Model.parrottV 1 * Model.parrottV 5) := by group
        _ = Model.hatX ^ 3 * (Model.parrottV 1 * Model.parrottV 5) := by rw [hX3]
  have := hd.conj_lift_eq hyC hXD hX3D h
  rw [d.lift_pow hXD] at this
  exact this

theorem IsV1.mem_M (hd : d.Hyp) {y₁ : G} (hy : IsV1 d z₀ y₁) : y₁ ∈ d.M := by
  obtain ⟨-, -, hyC, hρ⟩ := hy
  have hED : Model.hatE ≤ titsD := Model.hatE_le_titsJ.trans titsJ_le_titsD
  show y₁ ∈ normalizer ((d.liftSub Model.hatE ⊔ zpowers d.t : Subgroup G) : Set G)
  rw [hd.mem_normalizer_tSup_iff hED hyC]
  have hmem : ∀ i, Model.parrottV i ∈ normalizer (Model.hatE : Set (Equiv.Perm (Fin 1755))) :=
    fun i => Model.twoF4H_le_normalizer_hatE (Model.twoF4S_le_twoF4H (Model.parrottV_mem_twoF4S i))
  rcases hρ with h | h
  · rw [h]
    exact hmem 1
  · rw [h]
    exact mul_mem (hmem 1) (hmem 5)

theorem IsV1.mem_CMt (hd : d.Hyp) {y₁ : G} (hy : IsV1 d z₀ y₁) : y₁ ∈ CMt d :=
  mem_inf.2 ⟨hy.mem_M hd, hy.mem_C⟩

theorem IsV1.pow_four (hd : d.Hyp) (hz : d.S56Z0 z₀) {y₁ : G} (hy : IsV1 d z₀ y₁) :
    y₁ ^ 4 = 1 := by
  obtain ⟨-, hyz, hyC, hρ⟩ := hy
  have hv1 : Model.parrottV 1 ^ 4 = 1 := by
    have := Model.orderOf_parrottV (i := 1) le_rfl (by norm_num)
    rw [if_pos (by decide)] at this
    rw [← this]
    exact pow_orderOf_eq_one _
  have hv5 : Model.parrottV 5 ^ 4 = 1 := by
    have := Model.orderOf_parrottV (i := 5) (by norm_num) (by norm_num)
    rw [if_pos (by decide)] at this
    rw [← this]
    exact pow_orderOf_eq_one _
  have hcomm : Model.parrottV 1 * Model.parrottV 5 = Model.parrottV 5 * Model.parrottV 1 :=
    Model.parrottV_commute le_rfl (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide)
  have hρ4 : (d.ρ ⟨y₁, hyC⟩ : Equiv.Perm (Fin 1755)) ^ 4 = 1 := by
    rcases hρ with h | h
    · rw [h]
      exact hv1
    · rw [h, (Commute.mul_pow (show Commute (Model.parrottV 1) (Model.parrottV 5) from hcomm)),
        hv1, hv5, one_mul]
  have hC4 : y₁ ^ 4 ∈ centralizer ({d.t} : Set G) := pow_mem hyC 4
  have hρ' : (d.ρ ⟨y₁ ^ 4, hC4⟩ : Equiv.Perm (Fin 1755)) = 1 := by
    have : (⟨y₁ ^ 4, hC4⟩ : centralizer ({d.t} : Set G)) = ⟨y₁, hyC⟩ ^ 4 := rfl
    rw [this, map_pow]
    exact hρ4
  have h1D : (d.ρ ⟨y₁ ^ 4, hC4⟩ : Equiv.Perm (Fin 1755)) ∈ titsD := by
    rw [hρ']
    exact one_mem _
  rcases hd.eq_lift_or hC4 h1D with h | h
  · rw [hρ', d.lift_one] at h
    exact h
  · rw [hρ', d.lift_one, mul_one] at h
    exfalso
    have hc : y₁ ^ 4 * z₀ = z₀ * y₁ ^ 4 :=
      (Commute.pow_left (show Commute y₁ z₀ from hyz) 4).eq
    rw [h] at hc
    exact t_not_comm_z0 hd hz hc

theorem y1_mem_Hg (h49 : d.Thm49Statement) (hd : d.Hyp) {y₁ : G} (hy : IsV1 d z₀ y₁) :
    y₁ ∈ Hg d := M_le_Hg h49 hd (hy.mem_M hd)

theorem IsV1.isFrob (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    {y₁ : G} (hy : IsV1 d z₀ y₁) : IsFrob (star d d.x₅) (star d y₁) := by
  refine ⟨star_x5_pow_five h49 hd, star_x5_ne_one h49 hd hz h10, ?_, ?_⟩
  · rw [star_eq, ← actFun_pow d.s56V (y1_mem_Hg h49 hd hy), hy.pow_four hd hz, actFun_one]
  · rw [star_eq, star_eq, ← actFun_conj d.s56V (y1_mem_Hg h49 hd hy) (x5_mem_Hg h49 hd),
      hy.conj_x5 hd, actFun_pow d.s56V (x5_mem_Hg h49 hd)]

end Base

end CFSG.LocalAnalysis.EvenBN.Tits.N
