module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem14Elt
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem9
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem14Elt
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem14Gam

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611Nat

theorem normalizer_ZS_le_of_centralizer_le_F4 (h432 : Stmt4_3_2_F4) (h : Hyp611Nat G T M L V n)
    (hZ : Subgroup.centralizer (ch6ZS T L V : Set G) ≤ M) :
    Subgroup.normalizer (ch6ZS T L V : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  rw [(h.normalizer_ZS_eq_F4 h432).2]
  refine sup_le (fun x hx => (h.normalizer_le h.ZS_ne_bot h.ZS_le
    ⟨hZ hx, Subgroup.centralizer_le_normalizer _ hx⟩).2) (inf_le_left.trans inf_le_right)

theorem lemma_6_1_14_five_F4 (h432 : Stmt4_3_2_F4) (h6110 : Stmt6_1_10_F4)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (h : Hyp611Nat G T M L V n) (hev : Even n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t)
    (hSyl : IsSylowIn 2 (T ⊓ Subgroup.normalizer
        ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G))
      (M ⊓ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
        Set G)))
    (hn : 2 < n) (g : G)
    (hA : conjSubgroup V g ≤
      Subgroup.centralizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G))
    (hVA : V ≤ Subgroup.normalizer (conjSubgroup V g : Set G))
    (hne : ⁅V, conjSubgroup V g⁆ ≠ ⊥) :
    ¬ Subgroup.centralizer (ch6ZS T L V : Set G) ≤ M := by
  intro hZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn4 : 4 ≤ n := by
    obtain ⟨k, hk⟩ := hev
    omega
  set U := V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  set LU := lOne L U with hLU
  set A := conjSubgroup V g with hAdef
  set B := conjSubgroup V g⁻¹ with hBdef
  have hV := h.toHyp611.isElemAbelian
  have hV2 : IsPGroup 2 V := F7.isPGroup_of_isElemAbelian hV
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => B2F.isElemAbelian_comm hV hx hy

  have hBN : B ≤ Subgroup.normalizer (V : Set G) := by
    have h1 := conjSubgroup_mono_left g⁻¹ hVA
    rwa [conjSubgroup_normalizer, conjSubgroup_conj_inv] at h1
  have hBC : ¬ B ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    apply hne
    have h1 := conjSubgroup_mono_left g hle
    rw [conjSubgroup_inv_conj, conjSubgroup_centralizer] at h1
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1

  have hNVM : Subgroup.normalizer (V : Set G) ≤ M :=
    le_of_isUniqueM_of_le_twoLocal (h.toHyp611.isUniqueM_F4 h432) h.toHyp611.sup_le_normalizer
      ⟨V, h.toHyp611.ne_bot, hV2, rfl⟩
  have hB2 : IsPGroup 2 B := isPGroup_conjSubgroup hV2 g⁻¹
  obtain ⟨m, hm, hBT⟩ := h.toHyp611.exists_conj_sylow (le_inf (hBN.trans hNVM) hBN) hB2
  have h₁ := h.conj_of_mem hm.1 hm.2
  set T₁ := T.map (MulAut.conj m).toMonoidHom with hT₁
  set Z := ch6ZS T₁ L V with hZdef
  have hs : ∀ hV : IsElemAbelian 2 V, sParam hV = n := fun hV =>
    ((h6110 _ T M L V n h).2.1 hV).1
  have hBS : B ≤ ch6S T₁ L V := h₁.le_S_of_le_conj hs le_rfl hBT (by rw [mQuot_self]; omega)
  have hZM : Subgroup.centralizer (Z : Set G) ≤ M :=
    h.toHyp611.centralizer_ZS_map_le hm.1 hm.2 hZ
  have hNZ := h₁.normalizer_ZS_le_of_centralizer_le_F4 h432 hZM
  have hZcard : Nat.card Z = 2 ^ n := h₁.card_ZS

  have hmB := (h6110 _ T M L V n h).2.2 g⁻¹ hBN hBC
  have hBcard : Nat.card B = 2 ^ n * 2 ^ n := by
    rw [hBdef, card_conjSubgroup]
    exact h.natural.card_eq
  have hBC' : Nat.card ↥(B ⊓ Subgroup.centralizer (V : Set G)) = 2 ^ n := by
    have h1 := card_eq_two_pow_mul hB2 (inf_le_left : B ⊓ Subgroup.centralizer (V : Set G) ≤ B)
    rw [hmB, hBcard] at h1
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) h1).symm
  have hUeq : V ⊓ Subgroup.centralizer (A : Set G) = U := by
    have hconj : conjSubgroup (B ⊓ Subgroup.centralizer (V : Set G)) g =
        V ⊓ Subgroup.centralizer (A : Set G) := by
      rw [conjSubgroup_inf, hBdef, conjSubgroup_inv_conj, conjSubgroup_centralizer]
    have hcard : Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) = 2 ^ n := by
      rw [← hconj, card_conjSubgroup, hBC']
    have hle : U ≤ V ⊓ Subgroup.centralizer (A : Set G) :=
      le_inf inf_le_left fun u hu => Subgroup.mem_centralizer_iff.mpr fun a ha =>
        (Subgroup.mem_centralizer_iff.mp (hA ha) u hu).symm
    exact (Subgroup.eq_of_le_of_card_ge hle
      (by rw [hcard, h.card_fix_of_fieldAut htT ht])).symm

  have hAL := h.commutator_mem_centralizer_of_le_F4 h432 h6110 h37 h39 htT ht hSyl hn4 hA
  obtain ⟨x₁, hx₁, x₂, hx₂, h11, h22, h12, ⟨v₁, hv₁, hm₁⟩, ⟨v₂, hv₂, hm₂⟩, ⟨v₃, hv₃, hm₃⟩⟩ :=
    h.exists_unipotent_pair htT ht hn4

  obtain ⟨w, hwV, hwZ⟩ : ∃ w ∈ V, w ∉ Z := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show V ≤ Z from fun x hx => hcon x hx)
    rw [hZcard, h.natural.card_eq] at this
    have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
    nlinarith
  set a := g⁻¹ * w * g with hadef
  have hga : g * a * g⁻¹ = w := by rw [hadef]; group
  have ha : a ∈ A := mem_conjSubgroup_iff.mpr (by rw [hga]; exact hwV)

  have hgv : ∀ v ∈ V, g * v * g⁻¹ ∈ B := fun v hv =>
    mem_conjSubgroup_iff.mpr (by simpa [mul_assoc] using hv)
  have hBZ : ∀ b ∈ B, ∀ z ∈ Z, b * z = z * b := fun b hb z hz =>
    (Subgroup.mem_centralizer_iff.mp (hBS hb).2 z hz).symm
  have hcommZ : ∀ b ∈ B, ∀ v ∈ V, b * v * b⁻¹ * v⁻¹ ∈ Z := by
    intro b hb v hv
    have h1 : ⁅v, b⁆ ∈ ⁅V, ch6S T₁ L V⁆ := Subgroup.commutator_mem_commutator hv (hBS hb)
    have h2 := Z.inv_mem (h₁.commutator_V_S_le h1)
    have e : (⁅v, b⁆)⁻¹ = b * v * b⁻¹ * v⁻¹ := by rw [commutatorElement_def]; group
    rwa [e] at h2

  have hφZ : ∀ v ∈ V, g * (v * a * v⁻¹ * a⁻¹) * g⁻¹ ∈ Z := by
    intro v hv
    have e : g * (v * a * v⁻¹ * a⁻¹) * g⁻¹ =
        (g * v * g⁻¹) * (g * a * g⁻¹) * (g * v * g⁻¹)⁻¹ * (g * a * g⁻¹)⁻¹ := by group
    rw [e, hga]
    exact hcommZ _ (hgv v hv) w hwV

  have hφmul : ∀ v ∈ V, ∀ v' ∈ V, g * ((v * v') * a * (v * v')⁻¹ * a⁻¹) * g⁻¹ =
      (g * (v * a * v⁻¹ * a⁻¹) * g⁻¹) * (g * (v' * a * v'⁻¹ * a⁻¹) * g⁻¹) := by
    intro v hv v' hv'
    have hc1 : (g * v * g⁻¹) * (g * (v' * a * v'⁻¹ * a⁻¹) * g⁻¹) =
        (g * (v' * a * v'⁻¹ * a⁻¹) * g⁻¹) * (g * v * g⁻¹) :=
      hBZ _ (hgv v hv) _ (hφZ v' hv')
    have hc2 := hVc _ (h₁.ZS_le (hφZ v hv)) _ (h₁.ZS_le (hφZ v' hv'))
    calc g * ((v * v') * a * (v * v')⁻¹ * a⁻¹) * g⁻¹ =
        ((g * v * g⁻¹) * (g * (v' * a * v'⁻¹ * a⁻¹) * g⁻¹) * (g * v * g⁻¹)⁻¹) *
          (g * (v * a * v⁻¹ * a⁻¹) * g⁻¹) := by group
      _ = (g * (v' * a * v'⁻¹ * a⁻¹) * g⁻¹) * (g * (v * a * v⁻¹ * a⁻¹) * g⁻¹) := by
          rw [hc1]; group
      _ = _ := hc2.symm

  have hφker : ∀ v ∈ V, g * (v * a * v⁻¹ * a⁻¹) * g⁻¹ = 1 → v ∈ U := by
    intro v hv h1
    have h2 : v * a = a * v := by
      have : v * a * v⁻¹ * a⁻¹ = 1 := by
        have := congrArg (fun x => g⁻¹ * x * g) h1
        simpa [mul_assoc] using this
      calc v * a = (v * a * v⁻¹ * a⁻¹) * (a * v) := by group
        _ = a * v := by rw [this, one_mul]
    rw [← hUeq]
    refine ⟨hv, ?_⟩

    have hb := hgv v hv
    have hbV : g * v * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
      by_contra hbV
      have heq := h₁.centralizer_singleton_eq_ZS (hBS hb) hbV
      apply hwZ
      have hw' : w ∈ V ⊓ Subgroup.centralizer ({g * v * g⁻¹} : Set G) := by
        refine ⟨hwV, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
        rw [Set.mem_singleton_iff.mp hy, ← hga]
        calc g * v * g⁻¹ * (g * a * g⁻¹) = g * (v * a) * g⁻¹ := by group
          _ = g * (a * v) * g⁻¹ := by rw [h2]
          _ = g * a * g⁻¹ * (g * v * g⁻¹) := by group
      rw [heq] at hw'
      exact hw'
    have h3 := conjSubgroup_mono_left g (Subgroup.zpowers_le.mpr hbV)
    rw [conjSubgroup_centralizer] at h3
    have h4 : v ∈ conjSubgroup (Subgroup.zpowers (g * v * g⁻¹)) g :=
      mem_conjSubgroup_iff.mpr (Subgroup.mem_zpowers _)
    have h5 := h3 h4
    rw [← hAdef] at h5
    exact h5

  have hequi : ∀ x ∈ LU, ∀ v ∈ V, (g * x * g⁻¹) * (g * (v * a * v⁻¹ * a⁻¹) * g⁻¹) *
      (g * x * g⁻¹)⁻¹ = g * ((x * v * x⁻¹) * a * (x * v * x⁻¹)⁻¹ * a⁻¹) * g⁻¹ := by
    intro x hx v hv
    have hxN : x ∈ Subgroup.normalizer (V : Set G) :=
      h.data.le_normalizer ((oTwoUpper_le _).trans inf_le_left hx)
    have hv' : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxN v).mp hv
    have hc := hAL a⁻¹ (A.inv_mem ha) x hx
    rw [inv_inv] at hc
    have hcv : (a⁻¹ * x * a * x⁻¹) * (x * v * x⁻¹)⁻¹ = (x * v * x⁻¹)⁻¹ * (a⁻¹ * x * a * x⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hc _ (V.inv_mem hv')).symm
    calc (g * x * g⁻¹) * (g * (v * a * v⁻¹ * a⁻¹) * g⁻¹) * (g * x * g⁻¹)⁻¹ =
        g * ((x * v * x⁻¹) * a * ((a⁻¹ * x * a * x⁻¹) * (x * v * x⁻¹)⁻¹) *
          (a⁻¹ * x * a * x⁻¹)⁻¹ * a⁻¹) * g⁻¹ := by group
      _ = g * ((x * v * x⁻¹) * a * ((x * v * x⁻¹)⁻¹ * (a⁻¹ * x * a * x⁻¹)) *
          (a⁻¹ * x * a * x⁻¹)⁻¹ * a⁻¹) * g⁻¹ := by rw [hcv]
      _ = g * ((x * v * x⁻¹) * a * (x * v * x⁻¹)⁻¹ * a⁻¹) * g⁻¹ := by group

  have hφsurj : ∀ z ∈ Z, ∃ v ∈ V, z = g * (v * a * v⁻¹ * a⁻¹) * g⁻¹ := by
    let φ : ↥V →* ↥Z :=
      { toFun := fun v => ⟨g * ((v : G) * a * (v : G)⁻¹ * a⁻¹) * g⁻¹, hφZ v v.2⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := fun v v' => Subtype.ext (hφmul v v.2 v' v'.2) }
    have hker : Nat.card φ.ker ≤ Nat.card U := by
      refine Nat.card_le_card_of_injective (fun v => ⟨((v : ↥V) : G), hφker _ (v : ↥V).2
        (congrArg Subtype.val (MonoidHom.mem_ker.mp v.2))⟩) ?_
      intro v v' hvv'
      have h1 := congrArg Subtype.val hvv'
      exact Subtype.ext (Subtype.ext h1)
    have hcardV : Nat.card V = Nat.card φ.ker * Nat.card φ.range := by
      rw [← Subgroup.index_ker, Subgroup.card_mul_index]
    have hrange : φ.range = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      apply le_antisymm (Subgroup.card_le_card_group _)
      rw [h.card_fix_of_fieldAut htT ht] at hker
      rw [hZcard]
      by_contra hlt
      push Not at hlt
      have : Nat.card V < 2 ^ n * 2 ^ n := by
        rw [hcardV]
        calc Nat.card φ.ker * Nat.card φ.range ≤ 2 ^ n * Nat.card φ.range :=
              Nat.mul_le_mul_right _ hker
          _ < 2 ^ n * 2 ^ n := Nat.mul_lt_mul_of_pos_left hlt (by positivity)
      rw [h.natural.card_eq] at this
      exact lt_irrefl _ this
    intro z hz
    have : (⟨z, hz⟩ : ↥Z) ∈ φ.range := by rw [hrange]; exact Subgroup.mem_top _
    obtain ⟨v, hv⟩ := this
    exact ⟨v, v.2, (congrArg Subtype.val hv).symm⟩

  have hLUZ : ∀ x ∈ LU, g * x * g⁻¹ ∈ Subgroup.normalizer (Z : Set G) := by
    have hfwd : ∀ x ∈ LU, ∀ z ∈ Z, (g * x * g⁻¹) * z * (g * x * g⁻¹)⁻¹ ∈ Z := by
      intro x hx z hz
      obtain ⟨v, hv, rfl⟩ := hφsurj z hz
      have hxN : x ∈ Subgroup.normalizer (V : Set G) :=
        h.data.le_normalizer ((oTwoUpper_le _).trans inf_le_left hx)
      rw [hequi x hx v hv]
      exact hφZ _ ((Subgroup.mem_normalizer_iff.mp hxN v).mp hv)
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨hfwd x hx z, fun hz => ?_⟩
    have := hfwd x⁻¹ (LU.inv_mem hx) _ hz
    simpa [mul_assoc] using this

  have hfix : ∀ x ∈ LU, x * x ∈ Subgroup.centralizer (V : Set G) →
      ∀ z ∈ Z, (g * x * g⁻¹) * ((g * x * g⁻¹) * z * (g * x * g⁻¹)⁻¹) * (g * x * g⁻¹)⁻¹ = z := by
    intro x hx hxx z hz
    obtain ⟨v, hv, rfl⟩ := hφsurj z hz
    have hxN : x ∈ Subgroup.normalizer (V : Set G) :=
      h.data.le_normalizer ((oTwoUpper_le _).trans inf_le_left hx)
    have hv' : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxN v).mp hv
    rw [hequi x hx v hv, hequi x hx _ hv']
    have e : x * (x * v * x⁻¹) * x⁻¹ = v := by
      have := Subgroup.mem_centralizer_iff.mp hxx v hv
      calc x * (x * v * x⁻¹) * x⁻¹ = (x * x) * v * (x * x)⁻¹ := by group
        _ = v * (x * x) * (x * x)⁻¹ := by rw [this]
        _ = v := by group
    rw [e]
  have hmove : ∀ x ∈ LU, ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∉ U →
      (g * x * g⁻¹) * (g * (v * a * v⁻¹ * a⁻¹) * g⁻¹) * (g * x * g⁻¹)⁻¹ ≠
        g * (v * a * v⁻¹ * a⁻¹) * g⁻¹ := by
    intro x hx v hv hvU heq
    have hxN : x ∈ Subgroup.normalizer (V : Set G) :=
      h.data.le_normalizer ((oTwoUpper_le _).trans inf_le_left hx)
    have hv' : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxN v).mp hv
    apply hvU
    apply hφker _ (V.mul_mem hv' (V.inv_mem hv))
    rw [hequi x hx v hv] at heq
    have h1 := hφmul _ hv' _ (V.inv_mem hv)
    have h2 := hφmul _ hv _ (V.inv_mem hv)
    rw [mul_inv_cancel] at h2
    have h3 : g * (1 * a * 1⁻¹ * a⁻¹) * g⁻¹ = 1 := by group
    rw [h3] at h2
    rw [h1, heq, ← h2]
  have hL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    hNVM.trans h.normal

  have hx₁Z := hLUZ x₁ hx₁
  have hx₂Z := hLUZ x₂ hx₂
  refine h₁.false_of_commuting_on_ZS (hNZ hx₁Z) (hNZ hx₂Z) (hL (hNZ hx₁Z)) (hL (hNZ hx₂Z))
    hx₁Z hx₂Z (hfix x₁ hx₁ h11) (hfix x₂ hx₂ h22) ?_ ⟨_, hφZ v₁ hv₁, hmove x₁ hx₁ v₁ hv₁ hm₁⟩
    ⟨_, hφZ v₂ hv₂, hmove x₂ hx₂ v₂ hv₂ hm₂⟩ ?_
  ·
    intro z hz
    obtain ⟨v, hv, rfl⟩ := hφsurj z hz
    have hx₁N : x₁ ∈ Subgroup.normalizer (V : Set G) :=
      h.data.le_normalizer ((oTwoUpper_le _).trans inf_le_left hx₁)
    have hx₂N : x₂ ∈ Subgroup.normalizer (V : Set G) :=
      h.data.le_normalizer ((oTwoUpper_le _).trans inf_le_left hx₂)
    have hv₁' : x₁ * v * x₁⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hx₁N v).mp hv
    have hv₂' : x₂ * v * x₂⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hx₂N v).mp hv
    rw [hequi x₂ hx₂ v hv, hequi x₁ hx₁ _ hv₂', hequi x₁ hx₁ v hv, hequi x₂ hx₂ _ hv₁']
    have e : x₁ * (x₂ * v * x₂⁻¹) * x₁⁻¹ = x₂ * (x₁ * v * x₁⁻¹) * x₂⁻¹ := by
      have hc := (Subgroup.mem_centralizer_iff.mp h12 _ (V.mul_mem (V.mul_mem
        (V.mul_mem hv₁' (V.inv_mem hv)) hv) (V.inv_mem hv))).symm
      have hc' := Subgroup.mem_centralizer_iff.mp h12 (x₂ * (x₁ * v * x₁⁻¹) * x₂⁻¹)
        ((Subgroup.mem_normalizer_iff.mp hx₂N _).mp hv₁')
      calc x₁ * (x₂ * v * x₂⁻¹) * x₁⁻¹ =
          (x₁ * x₂ * x₁⁻¹ * x₂⁻¹) * (x₂ * (x₁ * v * x₁⁻¹) * x₂⁻¹) *
            (x₁ * x₂ * x₁⁻¹ * x₂⁻¹)⁻¹ := by group
        _ = (x₂ * (x₁ * v * x₁⁻¹) * x₂⁻¹) * (x₁ * x₂ * x₁⁻¹ * x₂⁻¹) *
            (x₁ * x₂ * x₁⁻¹ * x₂⁻¹)⁻¹ := by rw [← hc']
        _ = x₂ * (x₁ * v * x₁⁻¹) * x₂⁻¹ := by group
    rw [e]
  ·
    refine ⟨_, hφZ v₃ hv₃, ?_⟩
    have hx₂N : x₂ ∈ Subgroup.normalizer (V : Set G) :=
      h.data.le_normalizer ((oTwoUpper_le _).trans inf_le_left hx₂)
    have hv₃' : x₂ * v₃ * x₂⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hx₂N v₃).mp hv₃
    have h1 := hmove (x₁ * x₂) (LU.mul_mem hx₁ hx₂) v₃ hv₃ hm₃
    rw [hequi x₂ hx₂ v₃ hv₃, hequi x₁ hx₁ _ hv₃']
    rw [hequi (x₁ * x₂) (LU.mul_mem hx₁ hx₂) v₃ hv₃] at h1
    simpa [mul_assoc] using h1

end Hyp611Nat

end CFSG.Quasithin.H13
