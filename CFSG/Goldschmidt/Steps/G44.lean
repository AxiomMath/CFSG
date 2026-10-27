module

public import CFSG.Goldschmidt.Basic
public import CFSG.Timmesfeld.Bridge.InvolutionSet
import CFSG.Goldschmidt.Steps.PropHSetup
import CFSG.Goldschmidt.Steps.Fusion
import CFSG.Goldschmidt.Steps.Completion
import CFSG.Goldschmidt.Steps.Balance
import CFSG.Timmesfeld.Bridge.SchurNarrow
import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure

public section

namespace CFSG.Goldschmidt.G44

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Assembly.Dichotomy

variable {G : Type} [Group G]

@[expose] def classSet (U : Subgroup G) : Set G :=
  {x | ∃ g u : G, u ∈ U ∧ u ≠ 1 ∧ x = g * u * g⁻¹}

theorem classSet_normal (U : Subgroup G) : IsNormalSet (classSet U) := by
  rintro g x ⟨h, u, hu, hu1, rfl⟩
  exact ⟨g * h, u, hu, hu1, by group⟩

theorem orderOf_conj' (h u : G) : orderOf (h * u * h⁻¹) = orderOf u := by
  have := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective u
  simpa [MulAut.conj_apply] using this

theorem classSet_involution {U : Subgroup G} (hU : IsElemAbelian 2 U) :
    IsInvolutionSet (classSet U) := by
  rintro x ⟨h, u, hu, hu1, rfl⟩
  rw [orderOf_conj']
  exact orderOf_eq_prime (hU.2 u hu) hu1

theorem closure_normal_of_isNormalSet {D : Set G} (hN : IsNormalSet D) :
    (Subgroup.closure D).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (hN g x hx)
  | one => simp
  | mul x y _ _ hx hy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]; exact Subgroup.inv_mem _ hx

theorem closure_classSet [IsSimpleGroup G] {U : Subgroup G} (hU : U ≠ ⊥) :
    Subgroup.closure (classSet U) = ⊤ := by
  have := closure_normal_of_isNormalSet (classSet_normal U)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.closure (classSet U)) with h | h
  · exfalso
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
    have : (u : G) ∈ Subgroup.closure (classSet U) :=
      Subgroup.subset_closure ⟨1, u, u.2, fun h1 => hu1 (Subtype.ext h1), by group⟩
    rw [h, Subgroup.mem_bot] at this
    exact hu1 (Subtype.ext this)
  · exact h

theorem conj_mem_of_mem_classSet {S U : Subgroup G}
    (hcl : fusionStronglyClosed (U : Set G) S) {x : G} (hx : x ∈ classSet U) {g : G}
    (hg : g⁻¹ * x * g ∈ S) : g⁻¹ * x * g ∈ U := by
  obtain ⟨h, u, hu, -, rfl⟩ := hx
  have e : g⁻¹ * (h * u * h⁻¹) * g = (h⁻¹ * g)⁻¹ * u * (h⁻¹ * g) := by group
  rw [e] at hg ⊢
  exact hcl u hu _ hg

theorem noPolar_classSet [Finite G] {S : Sylow 2 G} {U : Subgroup G} (hU : IsElemAbelian 2 U)
    (hcl : fusionStronglyClosed (U : Set G) (S : Subgroup G)) :
    Moufang.NoPolar (classSet U) := by
  intro x hx y hy hxy hne
  have hx2 : orderOf x = 2 := classSet_involution hU x hx
  have hy2 : orderOf y = 2 := classSet_involution hU y hy
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpx : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2]; norm_num)
  have hpy : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy2]; norm_num)
  have hcomm : ∀ w ∈ Subgroup.zpowers y, x * w * x⁻¹ = w := by
    rintro w ⟨k, rfl⟩
    simp only
    rw [(hxy.zpow_right k).eq]; group
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [hcomm z hz]; exact hz
    · intro hz
      have h := hcomm _ hz
      have h' : x⁻¹ * (x * z * x⁻¹) * x = x * z * x⁻¹ := by
        calc x⁻¹ * (x * z * x⁻¹) * x = x⁻¹ * (x * (x * z * x⁻¹) * x⁻¹) * x := by rw [h]
          _ = x * z * x⁻¹ := by group
      have hz' : z = x * z * x⁻¹ := by
        calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
          _ = x * z * x⁻¹ := h'
      rw [hz']; exact hz
  have hp : IsPGroup 2 (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hpx hpy hnorm
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  have hmemQ : ∀ z ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G),
      g⁻¹ * z * g ∈ (S : Subgroup G) := by
    intro z hz
    have hzQ : z ∈ (Q : Subgroup G) := hQ hz
    rw [← hg] at hzQ
    obtain ⟨s, hs, hseq⟩ := hzQ
    have : z = g * s * g⁻¹ := by rw [← hseq]; rfl
    rw [this]
    have e : g⁻¹ * (g * s * g⁻¹) * g = s := by group
    rw [e]; exact hs
  have hxS := hmemQ x (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  have hyS := hmemQ y (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have hxU := conj_mem_of_mem_classSet hcl hx hxS
  have hyU := conj_mem_of_mem_classSet hcl hy hyS
  have hprod : g⁻¹ * (x * y) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) := by group
  refine ⟨g, (g⁻¹ * x * g) * (g⁻¹ * y * g), U.mul_mem hxU hyU, ?_, ?_⟩
  · intro h1
    apply hne
    have : x * y = 1 := by
      have h2 : g⁻¹ * (x * y) * g = 1 := by rw [hprod]; exact h1
      have : x * y = g * (g⁻¹ * (x * y) * g) * g⁻¹ := by group
      rw [this, h2]; group
    have hxx : x * x = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx2, pow_two] at this
      exact this
    have hyy : y * y = 1 := by
      have := pow_orderOf_eq_one y
      rw [hy2, pow_two] at this
      exact this
    calc x = x * (y * y) := by rw [hyy, mul_one]
      _ = (x * y) * y := by group
      _ = y := by rw [this, one_mul]
  · rw [← hprod]; group

theorem g44
    [Finite G] [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) (A U : Subgroup G) (hAS : A ≤ S) (hA : IsMulCommutative A)
    (hAcl : fusionStronglyClosed (A : Set G) (S : Subgroup G)) (hUA : U ≤ A)
    (hmin : IsMinStronglyClosed (S : Subgroup G) U)
    (hse : ∀ M : Subgroup G, ¬ CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) :
    (⨆ v : {u : G // u ∈ U ∧ u ≠ 1}, Subgroup.centralizer ({v.1} : Set G)) = ⊤ := by
  obtain ⟨hUel, -, hNAU, -, -, -⟩ := N31 G hnab S A U hAS hA hAcl hUA hmin
  have hUcl : fusionStronglyClosed (U : Set G) (S : Subgroup G) := hmin.2.2.1
  have hself : ∀ w : G, w ∈ Subgroup.centralizer ({w} : Set G) :=
    fun w => Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hU1 : U ≠ ⊥ := hmin.2.1
  set H0 : Subgroup G := ⨆ v : {u : G // u ∈ U ∧ u ≠ 1}, Subgroup.centralizer ({v.1} : Set G)
    with hH0
  by_contra hne
  have hle : ∀ v : {u : G // u ∈ U ∧ u ≠ 1}, Subgroup.centralizer ({v.1} : Set G) ≤ H0 :=
    fun v => le_iSup (fun v : {u : G // u ∈ U ∧ u ≠ 1} => Subgroup.centralizer ({v.1} : Set G)) v
  have hconj : ∀ n ∈ Subgroup.normalizer (U : Set G), ∀ z ∈ H0, n * z * n⁻¹ ∈ H0 := by
    intro n hn z hz
    refine Subgroup.iSup_induction
      (fun v : {u : G // u ∈ U ∧ u ≠ 1} => Subgroup.centralizer ({v.1} : Set G))
      (C := fun z => n * z * n⁻¹ ∈ H0) hz ?_ ?_ ?_
    · intro v z hz
      have hv' : n * v.1 * n⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hn v.1).mp v.2.1
      have hv1 : n * v.1 * n⁻¹ ≠ 1 := by
        intro h1; apply v.2.2
        have : v.1 = n⁻¹ * (n * v.1 * n⁻¹) * n := by group
        rw [this, h1]; group
      refine hle ⟨n * v.1 * n⁻¹, hv', hv1⟩ ?_
      rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
      have e1 : n * z * n⁻¹ * (n * v.1 * n⁻¹) = n * (z * v.1) * n⁻¹ := by group
      have e2 : n * v.1 * n⁻¹ * (n * z * n⁻¹) = n * (v.1 * z) * n⁻¹ := by group
      simp only at hz ⊢
      rw [e1, e2, hz]
    · simp
    · intro x y hx hy
      have : n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by group
      show n * (x * y) * n⁻¹ ∈ H0
      rw [this]; exact H0.mul_mem hx hy
  set H : Subgroup G := Subgroup.normalizer (H0 : Set G) with hH
  have hNUH : Subgroup.normalizer (U : Set G) ≤ H := by
    intro n hn
    rw [hH, Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · exact hconj n hn z
    · intro hz
      have := hconj n⁻¹ (Subgroup.inv_mem _ hn) _ hz
      have e : n⁻¹ * (n * z * n⁻¹) * n⁻¹⁻¹ = z := by group
      rwa [e] at this
  have hH0H : H0 ≤ H := Subgroup.le_normalizer
  have hHne : H ≠ ⊤ := by
    intro htop
    have hn0 : H0.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H0 with h | h
    · obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
      have hu : (u : G) ∈ H0 :=
        hle ⟨u, u.2, fun h1 => hu1 (Subtype.ext h1)⟩ (hself _)
      rw [h, Subgroup.mem_bot] at hu
      exact hu1 (Subtype.ext hu)
    · exact hne h
  have hNAH : Subgroup.normalizer (A : Set G) ≤ H := hNAU.trans hNUH
  have hkey : ∀ x ∈ classSet U, x ∈ H → Subgroup.centralizer ({x} : Set G) ≤ H := by
    rintro x ⟨g, u, hu, hu1, rfl⟩ hxH
    have huH : u ∈ H := hH0H (hle ⟨u, hu, hu1⟩ (hself u))
    have hgu : g⁻¹ * (g * u * g⁻¹) * g = u := by group
    have h2 : ∃ k : ℕ, (g * u * g⁻¹) ^ (2 ^ k) = 1 := by
      refine ⟨1, ?_⟩
      have := hUel.2 u hu
      rw [pow_one, ← orderOf_dvd_iff_pow_eq_one, orderOf_conj', orderOf_dvd_iff_pow_eq_one]
      exact this
    obtain ⟨h, hh, hhx⟩ :=
      N5a G S A H hAS hA hAcl hNAH (g * u * g⁻¹) g hxH (by rw [hgu]; exact huH) h2
    rw [hgu] at hhx
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    have hc' : h⁻¹ * c * h ∈ Subgroup.centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hhx]
      have e1 : h⁻¹ * c * h * (h⁻¹ * (g * u * g⁻¹) * h) =
          h⁻¹ * (c * (g * u * g⁻¹)) * h := by group
      have e2 : h⁻¹ * (g * u * g⁻¹) * h * (h⁻¹ * c * h) =
          h⁻¹ * ((g * u * g⁻¹) * c) * h := by group
      rw [e1, e2, hc]
    have := hH0H (hle ⟨u, hu, hu1⟩ hc')
    have e : c = h * (h⁻¹ * c * h) * h⁻¹ := by group
    rw [e]; exact H.mul_mem (H.mul_mem hh this) (H.inv_mem hh)
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
  have huD : (u : G) ∈ classSet U := ⟨1, u, u.2, fun h1 => hu1 (Subtype.ext h1), by group⟩
  have huH : (u : G) ∈ H :=
    hH0H (hle ⟨u, u.2, fun h1 => hu1 (Subtype.ext h1)⟩ (hself _))
  have hreach : ∀ y, Reach (classSet U) (u : G) y → y ∈ H := by
    intro y hy
    induction hy with
    | refl => exact huH
    | tail _ hbc ih =>
        obtain ⟨hb, -, hcomm⟩ := hbc
        exact hkey _ hb ih (Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq.symm)
  have hout : ∃ y ∈ classSet U, y ∉ H := by
    by_contra hcon
    push Not at hcon
    apply hHne
    rw [eq_top_iff, ← closure_classSet hU1]
    exact (Subgroup.closure_le H).mpr hcon
  obtain ⟨y, hyD, hyH⟩ := hout
  have hdisc : Disconnected (classSet U) := ⟨u, huD, y, hyD, fun hr => hyH (hreach y hr)⟩
  have hSE := asc73For_of CFSG.ShultStronglyClosedTI.theoremTwo schurNarrowInput G
    (classSet U) (classSet_normal U) (classSet_involution hUel) (closure_classSet hU1)
    (noPolar_classSet hUel hUcl) hdisc u huD
  exact hse _ hSE

theorem g44'
    [Finite G] [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) (A U : Subgroup G) (hAS : A ≤ S) (hA : IsMulCommutative A)
    (hAcl : fusionStronglyClosed (A : Set G) (S : Subgroup G)) (hUA : U ≤ A)
    (hmin : IsMinStronglyClosed (S : Subgroup G) U)
    (hse : ∀ M : Subgroup G, ¬ CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M)
    (H : Subgroup G) (hH : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ H) :
    H = ⊤ := by
  have h := g44 hnab S A U hAS hA hAcl hUA hmin hse
  rw [eq_top_iff, ← h]
  exact iSup_le fun v => hH v.1 v.2.1 v.2.2

theorem corX_false
    [Finite G] [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hIH : IH (Nat.card G))
    (S : Sylow 2 G) (A U : Subgroup G) (hAS : A ≤ S) (hA : IsMulCommutative A)
    (hAcl : fusionStronglyClosed (A : Set G) (S : Subgroup G)) (hUA : U ≤ A)
    (hmin : IsMinStronglyClosed (S : Subgroup G) U) (h8 : 8 ≤ Nat.card U)
    (hK : ∀ w ∈ U, w ≠ 1 → let M := normalClosureIn (Subgroup.centralizer ({w} : Set G)) U
      goldschmidtLayer (M ⧸ goldschmidtOddCore M) = ⊥)
    (hse : ∀ M : Subgroup G, ¬ CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) : False := by
  obtain ⟨hUel, -, -, -, -, -⟩ := N31 G hnab S A U hAS hA hAcl hUA hmin
  have hUcl : fusionStronglyClosed (U : Set G) (S : Subgroup G) := hmin.2.2.1
  have hU1 : U ≠ ⊥ := hmin.2.1
  obtain ⟨hodd, -, -, hCY, -, -, -, -, hTI⟩ :=
    N37_of N36 G hnab hIH S A U hAS hA hAcl hUA hmin h8 hK
  by_cases hW : oddCoreSpan U = ⊥
  · have hti : fusionIsTI U := hTI.mpr (by rw [hW]; exact Subgroup.commutator_bot_left _)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hCN := (isTI_iff_centralizer_le_normalizer S hmin.1 hUcl hUel.1).mp hti
    have htop := g44' hnab S A U hAS hA hAcl hUA hmin hse _ hCN
    have hn : U.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal U with h | h
    · exact hU1 h
    · obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have ha : a ∈ U := h ▸ Subgroup.mem_top a
      have hb : b ∈ U := h ▸ Subgroup.mem_top b
      have := hUel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
      exact congrArg Subtype.val this
  · have htop := g44' hnab S A U hAS hA hAcl hUA hmin hse _ hCY
    have hn : (oddCoreSpan U).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (oddCoreSpan U) with h | h
    · exact hW h
    · rw [h, Subgroup.card_top] at hodd
      obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
      have hu2 : orderOf (u : G) = 2 :=
        orderOf_eq_prime (hUel.2 u u.2) (fun h1 => hu1 (Subtype.ext h1))
      have hdvd : 2 ∣ Nat.card G := hu2 ▸ orderOf_dvd_natCard (u : G)
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

end CFSG.Goldschmidt.G44
