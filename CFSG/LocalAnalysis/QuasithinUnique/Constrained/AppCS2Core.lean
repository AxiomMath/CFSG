module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Split
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2AU
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs25

public section

namespace CFSG.QuasithinUnique.AppCS2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.DoubleA3 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

omit [Finite G] in
theorem J_le_baum (S : Subgroup G) : thompsonJ S ≤ baum S := C5.thompsonJ_le_baum' S

omit [Finite G] in
theorem Z0_comm_J {S : Subgroup G} {z : G} (hz : z ∈ omegaOneCenterOf (thompsonJ S)) {j : G}
    (hj : j ∈ thompsonJ S) : j * z = z * j :=
  Subgroup.mem_centralizer_iff.1
    (((Subgroup.closure_le _).mpr (fun _ hx => hx.1) : omegaOneCenterOf (thompsonJ S) ≤
      centerOf (thompsonJ S)) hz).2 j hj

omit [Finite G] in
theorem s2SI_le_N_X : s2SI S L ≤ normalizer ((L ⊔ baum S : Subgroup G) : Set G) := fun _ hg =>
  C1.mem_normalizer_sup hg.2 (normalizer_le_normalizer_baum S (Subgroup.le_normalizer hg.1))

namespace Dbl

variable {t : G} (D : Dbl T M H S L t)
include D

theorem nonempty_std :
    Nonempty {P : A5Pi L // P.im (thompsonJ S) = Estd ∧ P.im (s2SI S L) = Dstd ∧
      P.im (L ⊔ thompsonJ S) = ⊤} := by
  obtain ⟨P⟩ := nonempty_a5pi D.hL D.h5
  obtain ⟨P', h1, h2, h3⟩ := D.exists_std P
  exact ⟨⟨P', h1, h2, h3⟩⟩

theorem hBN : baum S ≤ normalizer (L : Set G) := by
  obtain ⟨⟨P, hJ, -, -⟩⟩ := D.nonempty_std
  exact D.baum_le_normalizer P hJ

theorem hBS₁ : baum S ≤ s2SI S L := fun _ hb => ⟨hb.1, D.hBN hb⟩

theorem isPGroup_baum : IsPGroup 2 (baum S) := D.hcs.sylow.2.1.to_le inf_le_left

theorem hXN : L ⊔ baum S ≤ normalizer (L : Set G) := sup_le Subgroup.le_normalizer D.hBN

theorem Q1_inf_centralizer :
    (L ⊔ baum S) ⊓ centralizer (blockU L : Set G) = pCoreOf 2 (L ⊔ baum S) :=
  C1.inf_centralizer_blockU_eq D.hL le_sup_left D.hXN
    (fun _ hg => C1.exists_pow_mem_of_mem_sup D.isPGroup_baum D.hBN hg)

theorem U_le_Q1 : blockU L ≤ pCoreOf 2 (L ⊔ baum S) := by
  rw [← D.Q1_inf_centralizer]
  intro u hu
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left (D.blockU_le_L hu),
    Subgroup.mem_centralizer_iff.2 fun v hv => blockU_comm_blockU D.hL hv hu⟩

theorem Z0_decomp (P : A5Pi L) {z : G} (hz : z ∈ omegaOneCenterOf (thompsonJ S)) :
    ∃ u ∈ blockU L ⊓ centralizer (thompsonJ S : Set G),
      (∀ γ ∈ L, γ * (u * z) = (u * z) * γ) ∧ u * z ∈ omegaOneCenterOf (thompsonJ S) := by
  have hzQ : z ∈ pCoreOf 2 H := D.omegaOneCenter_le_pCoreOf P.toPiData hz
  have hbb : ∀ ℓ ∈ L, z * ℓ * z⁻¹ * ℓ⁻¹ ∈ blockU L := C56.bb1 D.hcs z hzQ
  have hqC : ∀ u ∈ blockU L, z * u = u * z := fun u hu => D.Q_comm_U0 hzQ (Subgroup.mem_sup_left hu)
  obtain ⟨u, hu, hcent⟩ := exists_split_abs D.hL D.h5 P hbb hqC
  have hJ : ∀ j ∈ thompsonJ S, j * u = u * j := by
    intro j hj
    have hjN : j ∈ normalizer (L : Set G) := D.thompsonJ_le_N hj
    have hjU : j * u * j⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.1 (C1.mem_normalizer_blockU hjN) u).1 hu
    have hjz : j * z * j⁻¹ = z := by
      calc j * z * j⁻¹ = (z * j) * j⁻¹ := by rw [Z0_comm_J hz hj]
        _ = z := by group
    have hc : ∀ γ ∈ L, γ * ((j * u * j⁻¹) * z) = ((j * u * j⁻¹) * z) * γ := by
      intro γ hγ
      have hγ' : j⁻¹ * γ * j ∈ L := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hjN) γ).1 hγ
        simpa using this
      have h1 := hcent _ hγ'
      have e1 : γ * ((j * u * j⁻¹) * z) = j * ((j⁻¹ * γ * j) * (u * z)) * j⁻¹ := by
        calc γ * ((j * u * j⁻¹) * z) = γ * ((j * u * j⁻¹) * (j * z * j⁻¹)) := by rw [hjz]
          _ = j * ((j⁻¹ * γ * j) * (u * z)) * j⁻¹ := by group
      have e2 : ((j * u * j⁻¹) * z) * γ = j * ((u * z) * (j⁻¹ * γ * j)) * j⁻¹ := by
        calc ((j * u * j⁻¹) * z) * γ = ((j * u * j⁻¹) * (j * z * j⁻¹)) * γ := by rw [hjz]
          _ = j * ((u * z) * (j⁻¹ * γ * j)) * j⁻¹ := by group
      rw [e1, e2, h1]
    have hmem : (j * u * j⁻¹ * z) * (u * z)⁻¹ ∈ blockZ L := by
      have e : (j * u * j⁻¹ * z) * (u * z)⁻¹ = (j * u * j⁻¹) * u⁻¹ := by group
      have hmU : (j * u * j⁻¹ * z) * (u * z)⁻¹ ∈ blockU L := by
        rw [e]; exact (blockU L).mul_mem hjU ((blockU L).inv_mem hu)
      refine ⟨hmU, Subgroup.mem_centralizer_iff.2 fun γ hγ => ?_⟩
      have h1 := hc γ hγ
      have h2 := hcent γ hγ
      have h3 : (u * z)⁻¹ * γ = γ * (u * z)⁻¹ := by
        calc (u * z)⁻¹ * γ = (u * z)⁻¹ * (γ * (u * z)) * (u * z)⁻¹ := by group
          _ = (u * z)⁻¹ * ((u * z) * γ) * (u * z)⁻¹ := by rw [h2]
          _ = γ * (u * z)⁻¹ := by group
      calc γ * ((j * u * j⁻¹ * z) * (u * z)⁻¹)
          = (γ * (j * u * j⁻¹ * z)) * (u * z)⁻¹ := by group
        _ = ((j * u * j⁻¹ * z) * γ) * (u * z)⁻¹ := by rw [h1]
        _ = (j * u * j⁻¹ * z) * (γ * (u * z)⁻¹) := by group
        _ = (j * u * j⁻¹ * z) * ((u * z)⁻¹ * γ) := by rw [h3]
        _ = ((j * u * j⁻¹ * z) * (u * z)⁻¹) * γ := by group
    rw [blockZ_eq_bot_of_alt5 D.hL D.h5] at hmem
    have h1 : j * u * j⁻¹ * z * (u * z)⁻¹ = 1 := Subgroup.mem_bot.1 hmem
    have h2 : j * u * j⁻¹ = u := by
      have e : j * u * j⁻¹ * z * (u * z)⁻¹ = (j * u * j⁻¹) * u⁻¹ := by group
      rw [e] at h1
      exact mul_inv_eq_one.1 h1
    calc j * u = (j * u * j⁻¹) * j := by group
      _ = u * j := by rw [h2]
  have huF : u ∈ blockU L ⊓ centralizer (thompsonJ S : Set G) :=
    ⟨hu, Subgroup.mem_centralizer_iff.2 hJ⟩
  exact ⟨u, huF, hcent, mul_mem (D.F1_le_Z0 huF) hz⟩


theorem Q1_le_s2SI : pCoreOf 2 (L ⊔ baum S) ≤ s2SI S L := by
  set Q₁ := pCoreOf 2 (L ⊔ baum S) with hQ₁
  have hQ₁2 : IsPGroup 2 Q₁ := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _
  have hS₁N : s2SI S L ≤ normalizer (Q₁ : Set G) := fun g hg =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (L ⊔ baum S) (s2SI_le_N_X hg)
  have hQX : Q₁ ≤ L ⊔ s2SI S L :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans (sup_le_sup_left D.hBS₁ L)
  have hP : IsPGroup 2 ↥(Q₁ ⊔ s2SI S L) := by
    intro g
    obtain ⟨k, hk⟩ := C1.exists_pow_mem_of_mem_sup D.isPGroup_s2SI hS₁N g.2
    obtain ⟨m, hm⟩ := C1.exists_pow_eq_one_of_isPGroup hQ₁2 hk
    refine ⟨k + m, Subtype.ext ?_⟩
    have : (g : G) ^ 2 ^ (k + m) = 1 := by
      rw [pow_add, pow_mul]; exact hm
    simpa using this
  have hEq := D.isSylowTwoOf_s2SI_sup.eq_of_le (le_sup_right : s2SI S L ≤ Q₁ ⊔ s2SI S L)
    (sup_le hQX le_sup_right) hP
  exact le_sup_left.trans hEq.le

theorem Q1_le_baum : pCoreOf 2 (L ⊔ baum S) ≤ baum S := by
  intro q hq
  have hqS : q ∈ S := (D.Q1_le_s2SI hq).1
  refine ⟨hqS, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
  have hqX : q ∈ L ⊔ baum S := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _ hq
  have hqX' : q ∈ ((baum S ⊔ L : Subgroup G) : Set G) := by rw [sup_comm]; exact hqX
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (baum S) L D.hBN] at hqX'
  obtain ⟨b, hb, ℓ, hℓ, hbℓ⟩ := hqX'
  have hbℓ' : b * ℓ = q := hbℓ
  obtain ⟨⟨P, -, -, -⟩⟩ := D.nonempty_std
  obtain ⟨u, huF, huC, huZ⟩ := D.Z0_decomp P hz
  have hqC : ∀ w ∈ blockU L, (b * ℓ) * w = w * (b * ℓ) := by
    intro w hw
    have h1 : q ∈ (L ⊔ baum S) ⊓ centralizer (blockU L : Set G) := by
      rw [D.Q1_inf_centralizer]; exact hq
    rw [hbℓ']
    exact (Subgroup.mem_centralizer_iff.1 h1.2 w hw).symm
  have hbZ : ∀ w ∈ omegaOneCenterOf (thompsonJ S), w * b = b * w := fun w hw =>
    Subgroup.mem_centralizer_iff.1 hb.2 w hw
  have huZ' : (u : G) ∈ omegaOneCenterOf (thompsonJ S) := D.F1_le_Z0 huF
  have hℓu : ℓ * u = u * ℓ := by
    have h1 := hqC u huF.1
    have h2 := hbZ u huZ'
    calc ℓ * u = b⁻¹ * (b * ℓ * u) := by group
      _ = b⁻¹ * (u * (b * ℓ)) := by rw [h1]
      _ = b⁻¹ * ((u * b) * ℓ) := by group
      _ = b⁻¹ * ((b * u) * ℓ) := by rw [h2]
      _ = u * ℓ := by group
  have hℓd : ℓ * (u * z) = (u * z) * ℓ := huC ℓ hℓ
  have hℓz : ℓ * z = z * ℓ := by
    have : u * (ℓ * z) = u * (z * ℓ) := by
      calc u * (ℓ * z) = (u * ℓ) * z := by group
        _ = (ℓ * u) * z := by rw [hℓu]
        _ = ℓ * (u * z) := by group
        _ = (u * z) * ℓ := hℓd
        _ = u * (z * ℓ) := by group
    exact mul_left_cancel this
  rw [← hbℓ']
  calc z * (b * ℓ) = (z * b) * ℓ := by group
    _ = (b * z) * ℓ := by rw [hbZ z hz]
    _ = b * (z * ℓ) := by group
    _ = b * (ℓ * z) := by rw [hℓz]
    _ = (b * ℓ) * z := by group

theorem Q1_eq_inf :
    pCoreOf 2 (L ⊔ baum S) = baum S ⊓ centralizer (blockU L : Set G) := by
  apply le_antisymm
  · intro q hq
    have h1 : q ∈ (L ⊔ baum S) ⊓ centralizer (blockU L : Set G) := by
      rw [D.Q1_inf_centralizer]; exact hq
    exact ⟨D.Q1_le_baum hq, h1.2⟩
  · intro q hq
    rw [← D.Q1_inf_centralizer]
    exact ⟨mem_sup_right hq.1, hq.2⟩

theorem Q1_eq_sup :
    pCoreOf 2 (L ⊔ baum S) = blockU L ⊔ s2I S L := by
  apply le_antisymm
  · intro q hq
    obtain ⟨⟨P, -, -, -⟩⟩ := D.nonempty_std
    have hqX : q ∈ L ⊔ baum S := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _ hq
    have h1 : q ∈ (L ⊔ baum S) ⊓ centralizer (blockU L : Set G) := by
      rw [D.Q1_inf_centralizer]; exact hq
    have hbb : ∀ ℓ ∈ L, q * ℓ * q⁻¹ * ℓ⁻¹ ∈ blockU L := fun ℓ hℓ =>
      C1.commutator_mem_blockU_of_mem_blockQ D.hL (fun l hl =>
        C1.commutator_mem_blockQ_of_mem_pCoreOf le_sup_left D.hXN hq hl) ℓ hℓ
    have hqC : ∀ u ∈ blockU L, q * u = u * q := fun u hu =>
      (Subgroup.mem_centralizer_iff.1 h1.2 u hu).symm
    obtain ⟨u, hu, hcent⟩ := exists_split_abs D.hL D.h5 P hbb hqC
    have hdQ : u * q ∈ pCoreOf 2 (L ⊔ baum S) := mul_mem (D.U_le_Q1 hu) hq
    have hdB : u * q ∈ baum S := D.Q1_le_baum hdQ
    have hdD : u * q ∈ s2I S L := ⟨hdB, Subgroup.mem_centralizer_iff.2 fun γ hγ => hcent γ hγ⟩
    have e : q = u⁻¹ * (u * q) := by group
    rw [e]
    exact mul_mem (mem_sup_left (inv_mem hu)) (mem_sup_right hdD)
  · refine sup_le D.U_le_Q1 ?_
    intro d hd
    rw [D.Q1_eq_inf]
    refine ⟨hd.1, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
    exact Subgroup.mem_centralizer_iff.1 hd.2 u (D.blockU_le_L hu)

theorem internalDirect : IsInternalDirect (blockU L) (s2I S L) (pCoreOf 2 (L ⊔ baum S)) := by
  refine ⟨?_, ?_, D.Q1_eq_sup.symm⟩
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (Subgroup.mem_centralizer_iff.1 hd.2 u (D.blockU_le_L hu)).symm
  · refine eq_bot_iff.2 fun x hx => ?_
    have hxZ : x ∈ blockZ L := ⟨hx.1, Subgroup.mem_centralizer_iff.2 fun l hl =>
      Subgroup.mem_centralizer_iff.1 hx.2.2 l hl⟩
    rw [blockZ_eq_bot_of_alt5 D.hL D.h5] at hxZ
    exact hxZ

theorem map_subgroupOf_eq_im (P : PiData L) {K : Subgroup G} (hKX : K ≤ L ⊔ baum S) :
    (K.subgroupOf (L ⊔ baum S)).map (P.π.comp (Subgroup.inclusion D.hXN)) = P.im K := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact P.pi_mem_im (K := K) (y := Subgroup.inclusion D.hXN x) (Subgroup.mem_subgroupOf.1 hx)
  · intro hg
    obtain ⟨y, hy, rfl⟩ := (P.mem_im).1 hg
    exact ⟨⟨(y : G), hKX hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩

theorem core_B (P : A5Pi L) :
    ∃ τ₁ τ₂ : Perm (Fin 5), τ₁.IsSwap ∧ τ₂.IsSwap ∧ τ₁.Disjoint τ₂ ∧
      P.im (thompsonJ S) = Subgroup.closure {τ₁, τ₂} ∧
      P.im (baum S) = Subgroup.closure {τ₁, τ₂} ∧ P.im (L ⊔ baum S) = ⊤ := by
  obtain ⟨τ₁, τ₂, hτ₁, hτ₂, hdisj, hJeq, -, htop, -, hfix⟩ := D.core_J P
  have hBJ : P.im (baum S) ≤ P.im (thompsonJ S) := by
    intro g hg
    obtain ⟨b, hb, rfl⟩ := (P.mem_im).1 hg
    apply hfix
    intro w hw
    set u : ↥(blockU L) := P.β.symm (Multiplicative.ofAdd w) with hu
    have hwu : Multiplicative.toAdd (P.β u) = w := by simp [hu]
    have hcJ : ∀ y ∈ thompsonJ S, (y : G) * u = u * y := by
      intro y hy
      have hyN : y ∈ Subgroup.normalizer (L : Set G) := D.thompsonJ_le_N hy
      have hmem : y * (u : G) * y⁻¹ ∈ blockU L :=
        (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (L := L) hyN) u).mp u.2
      have h := P.hcomp ⟨y, hyN⟩ u ⟨_, hmem⟩ rfl
      have hfy : vact (P.π ⟨y, hyN⟩) w = w := hw _ (P.pi_mem_im (K := thompsonJ S) hy)
      rw [hwu, hfy] at h
      have h' : Multiplicative.toAdd (P.β ⟨y * (u : G) * y⁻¹, hmem⟩) =
          Multiplicative.toAdd (P.β u) := by rw [h, hwu]
      have h2 : (⟨_, hmem⟩ : ↥(blockU L)) = u :=
        P.β.injective (Multiplicative.toAdd.injective h')
      have h3 : y * (u : G) * y⁻¹ = u := congrArg Subtype.val h2
      calc (y : G) * u = (y * u * y⁻¹) * y := by group
        _ = u * y := by rw [h3]
    have huF : (u : G) ∈ blockU L ⊓ centralizer (thompsonJ S : Set G) :=
      ⟨u.2, Subgroup.mem_centralizer_iff.2 hcJ⟩
    have huZ := D.F1_le_Z0 huF
    have hbc : (u : G) * b = b * u := Subgroup.mem_centralizer_iff.1 hb.2 u huZ
    have h := P.hcomp b u u (by
      show (u : G) = (b : G) * (u : G) * (b : G)⁻¹
      rw [← hbc]; group)
    rw [hwu] at h
    exact h.symm
  have hBeq : P.im (baum S) = P.im (thompsonJ S) := le_antisymm hBJ (P.im_mono (J_le_baum S))
  refine ⟨τ₁, τ₂, hτ₁, hτ₂, hdisj, hJeq, hBeq.trans hJeq, ?_⟩
  refine eq_top_iff.2 ?_
  rw [← htop]
  exact P.im_mono (sup_le_sup_left (J_le_baum S) L)

end Dbl


theorem lemmaC54_3_s2 : A5.LemmaC54_3_s2 := by
  intro G _ _ T M H S L hcs h5 hne
  obtain ⟨t, ⟨D⟩⟩ := exists_dbl hcs h5 hne
  refine ⟨D.hBN, D.U_le_Q1, D.Q1_eq_inf, D.internalDirect, ?_⟩
  intro α hα hαk
  obtain ⟨P, rfl⟩ := exists_a5pi D.hL h5 α hα hαk
  obtain ⟨τ₁, τ₂, hτ₁, hτ₂, hdisj, hJeq, hBeq, htop⟩ := D.core_B P
  have hXN := D.hXN
  refine ⟨P.π.comp (Subgroup.inclusion hXN), τ₁, τ₂, ?_, ?_, ?_, hτ₁, hτ₂, hdisj, ?_, ?_⟩
  · intro σ
    have hσ : σ ∈ P.im (L ⊔ baum S) := by rw [htop]; trivial
    obtain ⟨y, hy, rfl⟩ := (P.mem_im).1 hσ
    exact ⟨⟨(y : G), hy⟩, rfl⟩
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← D.Q1_inf_centralizer]
    constructor
    · intro hx
      refine ⟨x.2, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
      have h1 : (x : G) * u * (x : G)⁻¹ = u := (P.hker (Subgroup.inclusion hXN x)).1 hx u hu
      calc u * (x : G) = ((x : G) * u * (x : G)⁻¹) * x := by rw [h1]
        _ = x * u := by group
    · rintro ⟨-, hxc⟩
      apply (P.hker (Subgroup.inclusion hXN x)).2
      intro u hu
      have h1 := Subgroup.mem_centralizer_iff.1 hxc u hu
      calc (x : G) * u * (x : G)⁻¹ = (u * x) * (x : G)⁻¹ := by rw [h1]
        _ = u := by group
  · intro l hl
    exact P.hπα l hl
  · rw [D.map_subgroupOf_eq_im P.toPiData le_sup_right, hBeq]
  · rw [D.map_subgroupOf_eq_im P.toPiData ((J_le_baum S).trans le_sup_right), hJeq]

end CFSG.QuasithinUnique.AppCS2
