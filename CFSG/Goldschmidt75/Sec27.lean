module

public import CFSG.Goldschmidt75.Closure
public import CFSG.Timmesfeld.Bridge.SchurNarrow
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge

variable {G : Type} [Group G]

@[expose] def invClass (S : Subgroup G) : Set G :=
  {x | ∃ g s : G, s ∈ S ∧ s ≠ 1 ∧ s ^ 2 = 1 ∧ x = g * s * g⁻¹}

theorem invClass_normal (S : Subgroup G) : IsNormalSet (invClass S) := by
  rintro g x ⟨h, s, hs, hs1, hs2, rfl⟩
  exact ⟨g * h, s, hs, hs1, hs2, by group⟩

theorem orderOf_conj_eq (h u : G) : orderOf (h * u * h⁻¹) = orderOf u := by
  have := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective u
  simpa [MulAut.conj_apply] using this

theorem invClass_involution (S : Subgroup G) : IsInvolutionSet (invClass S) := by
  rintro x ⟨h, s, -, hs1, hs2, rfl⟩
  rw [orderOf_conj_eq]
  exact orderOf_eq_prime hs2 hs1

variable [Finite G]

omit [Finite G] in
theorem conj_mem_of_mem_invClass (T : Sylow 2 G) {S : Subgroup G}
    (hS : fusionStronglyClosed (S : Set G) T) {x g : G} (hx : x ∈ invClass S)
    (hxg : g⁻¹ * x * g ∈ (T : Subgroup G)) : g⁻¹ * x * g ∈ S := by
  obtain ⟨h, s, hs, -, -, rfl⟩ := hx
  have e : g⁻¹ * (h * s * h⁻¹) * g = (h⁻¹ * g)⁻¹ * s * (h⁻¹ * g) := by group
  rw [e] at hxg ⊢
  exact hS s hs _ hxg

theorem noPolar_invClass (T : Sylow 2 G) {S : Subgroup G}
    (hS : fusionStronglyClosed (S : Set G) T) : Moufang.NoPolar (invClass S) := by
  intro x hx y hy hxy hne
  have hx2 : orderOf x = 2 := invClass_involution S x hx
  have hy2 : orderOf y = 2 := invClass_involution S y hy
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpx : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2]; norm_num)
  have hpy : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy2]; norm_num)
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
      fun w hw => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        exact ((hxy.zpow_right k).eq).symm)
  have hp : IsPGroup 2 (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hpx hpy hnorm
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨y₀, hy₀⟩ := exists_conjSub_eq T Q
  have hmemT : ∀ z ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G),
      y₀⁻¹ * z * y₀ ∈ (T : Subgroup G) := by
    intro z hz
    have hzQ : z ∈ (Q : Subgroup G) := hQ hz
    have : y₀⁻¹ * z * y₀ ∈ conjSub y₀ (Q : Subgroup G) := conj_mem_conjSub hzQ
    rwa [hy₀] at this
  have hxS := conj_mem_of_mem_invClass T hS hx (hmemT x (mem_sup_left (mem_zpowers x)))
  have hyS := conj_mem_of_mem_invClass T hS hy (hmemT y (mem_sup_right (mem_zpowers y)))
  have hxx : x * x = 1 := by rw [← pow_two, ← hx2, pow_orderOf_eq_one]
  have hyy : y * y = 1 := by rw [← pow_two, ← hy2, pow_orderOf_eq_one]
  refine ⟨y₀, y₀⁻¹ * (x * y) * y₀, ?_, ?_, ?_, by group⟩
  · have e : y₀⁻¹ * (x * y) * y₀ = (y₀⁻¹ * x * y₀) * (y₀⁻¹ * y * y₀) := by group
    rw [e]; exact S.mul_mem hxS hyS
  · intro h1
    apply hne
    have hxy1 : x * y = 1 := by
      have : x * y = y₀ * (y₀⁻¹ * (x * y) * y₀) * y₀⁻¹ := by group
      rw [this, h1]; group
    calc x = x * (y * y) := by rw [hyy, mul_one]
      _ = (x * y) * y := by group
      _ = y := by rw [hxy1, one_mul]
  · have hc : x * y = y * x := hxy.eq
    rw [pow_two]
    calc y₀⁻¹ * (x * y) * y₀ * (y₀⁻¹ * (x * y) * y₀) = y₀⁻¹ * (x * (y * x) * y) * y₀ := by
          group
      _ = y₀⁻¹ * (x * (x * y) * y) * y₀ := by rw [hc]
      _ = 1 := by
          rw [show x * (x * y) * y = (x * x) * (y * y) by group, hxx, hyy]; group

theorem exists_central_involution (T : Sylow 2 G) {S : Subgroup G} (hST : S ≤ T)
    (hS : fusionStronglyClosed (S : Set G) T) (hS1 : S ≠ ⊥) :
    ∃ z ∈ S, orderOf z = 2 ∧ z ∈ centralizer ((T : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z₀, hz₀S, hz₀1, hz₀c⟩ := exists_mem_center T hST hS hS1
  set Z := S ⊓ centralizer ((T : Subgroup G) : Set G)
  have hZp : IsPGroup 2 Z := T.isPGroup'.to_le (inf_le_left.trans hST)
  have hZ1 : Nontrivial Z := ⟨⟨⟨z₀, hz₀S, hz₀c⟩, 1, fun h => hz₀1 (congrArg Subtype.val h)⟩⟩
  obtain ⟨k, hk, hcard⟩ := hZp.nontrivial_iff_card.mp hZ1
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2
    (by rw [hcard]; exact dvd_pow_self 2 (by omega))
  refine ⟨z, z.2.1, by rw [← Subgroup.orderOf_coe] at hz; exact hz, z.2.2⟩

theorem centralizers_eq_top_or_stronglyEmbedded
    (T : Sylow 2 G) {S : Subgroup G}
    (hST : S ≤ T) (hS : fusionStronglyClosed (S : Set G) T) (hS1 : S ≠ ⊥)
    (hgen : Subgroup.closure (invClass S) = ⊤) :
    (⨆ s : {s : G // s ∈ S ∧ s ≠ 1 ∧ s ^ 2 = 1}, centralizer ({s.1} : Set G)) = ⊤ ∨
      ∃ M : Subgroup G, CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hM, hse⟩ := hcon
  set M := ⨆ s : {s : G // s ∈ S ∧ s ≠ 1 ∧ s ^ 2 = 1}, centralizer ({s.1} : Set G)
  have hle : ∀ s ∈ S, s ≠ 1 → s ^ 2 = 1 → centralizer ({s} : Set G) ≤ M := fun s hs hs1 hs2 =>
    le_iSup (fun s : {s : G // s ∈ S ∧ s ≠ 1 ∧ s ^ 2 = 1} => centralizer ({s.1} : Set G))
      ⟨s, hs, hs1, hs2⟩
  obtain ⟨z, hzS, hz2, hzc⟩ := exists_central_involution T hST hS hS1
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; exact absurd hz2 (by norm_num)
  have hzsq : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
  have hSM : S ≤ M := fun s hs => hle z hzS hz1 hzsq
    (mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzc s (hST hs)))
  have hconjM : ∀ u ∈ invClass S, u ∈ M → ∃ m ∈ M, m⁻¹ * u * m ∈ S := by
    intro u hu huM
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨TM, hTM⟩ := ((T.isPGroup'.to_le hST).comap_subtype (K := M)).exists_le_sylow
    have hu2 : orderOf u = 2 := invClass_involution S u hu
    have hpu : IsPGroup 2 (zpowers (⟨u, huM⟩ : M)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hu2]; norm_num)
    obtain ⟨Q, hQ⟩ := hpu.exists_le_sylow
    obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M Q TM
    have huQ : (⟨u, huM⟩ : M) ∈ (Q : Subgroup M) := hQ (mem_zpowers _)
    have hmu : m * ⟨u, huM⟩ * m⁻¹ ∈ (TM : Subgroup M) := by
      rw [← hm, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨_, huQ, rfl⟩
    obtain ⟨T'', hT''⟩ := (TM.2.map M.subtype).exists_le_sylow
    have hSTM : S ≤ (TM : Subgroup M).map M.subtype := fun s hs =>
      ⟨⟨s, hSM hs⟩, hTM (by simpa [mem_subgroupOf] using hs), rfl⟩
    have hS'' := stronglyClosed_of_le_sylow T T'' hS (hSTM.trans hT'')
    refine ⟨(m : G)⁻¹, M.inv_mem m.2, ?_⟩
    have h1 : ((m : G)⁻¹)⁻¹ * u * (m : G)⁻¹ ∈ (T'' : Subgroup G) := by
      have := hT'' ⟨_, hmu, rfl⟩
      simpa using this
    exact conj_mem_of_mem_invClass T'' hS'' hu h1
  have hstepM : ∀ u ∈ invClass S, u ∈ M → ∀ v ∈ invClass S, Commute u v → v ∈ M := by
    intro u hu huM v hv huv
    obtain ⟨m, hm, hmu⟩ := hconjM u hu huM
    have hu2 : orderOf u = 2 := invClass_involution S u hu
    have hord : orderOf (m⁻¹ * u * m) = 2 := by
      have := orderOf_conj_eq m⁻¹ u
      rwa [inv_inv] at this ▸ hu2
    have hs1 : m⁻¹ * u * m ≠ 1 := fun h => by
      rw [h, orderOf_one] at hord; exact absurd hord (by norm_num)
    have hs2 : (m⁻¹ * u * m) ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
    have hvC : m⁻¹ * v * m ∈ centralizer ({m⁻¹ * u * m} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc m⁻¹ * v * m * (m⁻¹ * u * m) = m⁻¹ * (v * u) * m := by group
        _ = m⁻¹ * (u * v) * m := by rw [huv.eq]
        _ = m⁻¹ * u * m * (m⁻¹ * v * m) := by group
    have h1 := hle _ hmu hs1 hs2 hvC
    have e : v = m * (m⁻¹ * v * m) * m⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem hm h1) (M.inv_mem hm)
  have hzD : z ∈ invClass S := ⟨1, z, hzS, hz1, hzsq, by group⟩
  have hreach : ∀ y, Reach (invClass S) z y → y ∈ M := by
    intro y hy
    induction hy with
    | refl => exact hSM hzS
    | tail _ hbc ih =>
        obtain ⟨hb, hc, hcomm⟩ := hbc
        exact hstepM _ hb ih _ hc hcomm
  have hout : ∃ y ∈ invClass S, y ∉ M := by
    by_contra hcon
    push Not at hcon
    apply hM
    rw [eq_top_iff, ← hgen]
    exact (Subgroup.closure_le M).mpr hcon
  obtain ⟨y, hyD, hyM⟩ := hout
  have hdisc : Disconnected (invClass S) := ⟨z, hzD, y, hyD, fun hr => hyM (hreach y hr)⟩
  exact hse _ (asc73For_of CFSG.ShultStronglyClosedTI.theoremTwo schurNarrowInput G
    (invClass S) (invClass_normal S) (invClass_involution S) hgen (noPolar_invClass T hS)
    hdisc z hzD)

end CFSG.Goldschmidt75
