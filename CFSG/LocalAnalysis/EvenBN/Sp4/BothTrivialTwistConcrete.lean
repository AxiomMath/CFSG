module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwistSwap
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwistFinal
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwistBar
public import CFSG.LocalAnalysis.SteinbergSFSingleCommRootStandardTorus

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace BothTrivialTwistConcrete

open Subgroup CFSG.Blueprint CFSG.Open
open CFSG.LocalAnalysis.SymplecticFourStandard
open GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl FullCenterMutual BothTrivial BothTrivialHeisenberg
  BothTrivialClosure BothTrivialLayer BothTrivialRankOne BothTrivialSlice BothTrivialField
  BothTrivialCases BothTrivialTwist BothTrivialTwistSwap
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped MatrixGroups

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
local notation "𝐉[" i "]" => pull φ (axisTorus K i)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐗[" i "]" => (𝐅 ⊔ 𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐒" => (𝐗[Axis.one] ⊔ 𝐗[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
set_option quotPrecheck false in
local notation "𝐑[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐄[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓₀" => (𝐑[Axis.one] ⊔ 𝐑[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊[" i "]" => barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G))
set_option quotPrecheck false in
local notation "𝐖[" i "]" => (𝐅 ⊓ centralizer (𝐉[i] : Set G) : Subgroup G)

theorem mem_preBar_of_centralizer (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) {y : G} (hyL : y ∈ L)
    (hyU : y ∈ centralizer (𝐔[Axis.one] : Set G)) :
    y ∈ preBar 𝐗[Axis.one] (normalClosure (𝐊[Axis.one] : Set (BarM 𝐗[Axis.one]))) := by
  have hyC : y ∈ 𝐂 := h.setup.L_le hyL
  have hyX : y ∈ normalizer (𝐗[Axis.one] : Set G) :=
    mem_normalizer_X_of_mem_normalizer_U h hbt Axis.one hyC
      (Subgroup.centralizer_le_normalizer _ hyU)
  exact (mem_preBar hyX).mpr (subset_normalClosure
    ⟨⟨y, hyX⟩, mem_subgroupOf.mpr (mem_inf.mpr ⟨hyL, hyU⟩), rfl⟩)

theorem axisTorus_mem_centralizer (i : Axis) {j : G} (hj : j ∈ 𝐉[i]) :
    j ∈ centralizer (𝐔[i] : Set G) := by
  refine mem_centralizer_iff.mpr fun x hx => ?_
  have h1 := axisTorus_cent i hj hx
  calc x * j = j * (j⁻¹ * x * j) := by group
    _ = j * x := by rw [h1]

set_option quotPrecheck false in
local notation "𝐍" => preBar 𝐗[Axis.one]
  (normalClosure (𝐊[Axis.one] : Set (BarM 𝐗[Axis.one])))

theorem three_dvd_two_pow_two_mul (n : ℕ) : 3 ∣ 2 ^ (2 * n) - 1 := by
  have h1 : 4 ^ n ≡ 1 ^ n [MOD 3] := Nat.ModEq.pow n (by decide)
  rw [one_pow] at h1
  have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
  rw [pow_mul, h4]
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp h1.symm

theorem S_eq_aux (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) :
    ∀ s ∈ 𝐒, ∃ a ∈ 𝐗[Axis.one], ∃ b ∈ 𝐗[Axis.two], s = a * b := by
  intro s hs
  rw [← SetLike.mem_coe, ← X_mul_X h hbt] at hs
  obtain ⟨a, ha, b, hb, rfl⟩ := hs
  exact ⟨a, ha, b, hb, rfl⟩

theorem centre_le_aux (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) :
    ∀ x ∈ 𝐒, (∀ s ∈ 𝐒, s * x = x * s) → x ∈ 𝐅 := by
  intro x hx hc
  have hx' : (⟨x, hx⟩ : 𝐒) ∈ center 𝐒 := mem_center_iff.mpr fun g => Subtype.ext (hc g g.2)
  rw [← center_S h hbt]
  exact ⟨_, hx', rfl⟩

theorem card_X_aux (h : FCHyp L K n φ t) (i : Axis) :
    Nat.card 𝐗[i] = (2 ^ (2 * n)) ^ 3 := by
  rw [card_X h i, h.setup.card_K]
  ring

theorem card_F_aux (h : FCHyp L K n φ t) : Nat.card 𝐅 = (2 ^ (2 * n)) ^ 2 := by
  rw [card_F h, h.setup.card_K]
  ring

theorem S_le_N_aux (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (hSN : barSub 𝐗[Axis.one] 𝐒 ≤ normalClosure (𝐊[Axis.one] : Set (BarM 𝐗[Axis.one]))) {s : G}
    (hs : s ∈ 𝐒) : s ∈ 𝐍 :=
  (mem_preBar (S_le_normalizer_X h hbt Axis.one hs)).mpr
    (hSN ((mem_barSub_iff (X_le_S Axis.one) _).mpr hs))

theorem w_mem_aux (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) :
    𝐰[Axis.one] ∈ 𝐍 := by
  obtain ⟨-, -, -, -, -, hwcomm⟩ := w_facts h Axis.one
  exact mem_preBar_of_centralizer h hbt (w_mem_L Axis.one) (mem_centralizer_iff.mpr hwcomm)

theorem X₁_eq_aux (h : FCHyp L K n φ t) :
    ∀ x ∈ 𝐗[Axis.one], ∃ a ∈ 𝐅, ∃ b ∈ 𝐅, x = a * (𝐰[Axis.one] * b * 𝐰[Axis.one]⁻¹) := by
  intro x hx
  rw [← SetLike.mem_coe, ← F_mul_Fw' h Axis.one] at hx
  obtain ⟨a, ha, y, ⟨b, hb, rfl⟩, rfl⟩ := hx
  refine ⟨a, ha, b, hb, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, w_inv, inv_inv]

theorem cc_aux (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    {u : G} (huC : u ∈ 𝐂) (hU : ∀ x ∈ 𝐔[Axis.two], u * x * u⁻¹ ∈ 𝐔[Axis.one])
    (hu2 : u * u ∈ 𝐒) :
    ∀ z ∈ 𝐅, (∀ n ∈ 𝐍, n * z = z * n) → (∀ n ∈ 𝐍, u * n * u⁻¹ * z = z * (u * n * u⁻¹)) →
      z = 1 := by
  intro z hzF hz1 hz2
  have huL : u ∈ normalizer (L : Set G) := h.setup.cent_le huC
  have hUmap := map_U_swap hU
  have hJ1 : ∀ j ∈ 𝐉[Axis.one], j * z = z * j := fun j hj =>
    hz1 j (mem_preBar_of_centralizer h hbt (pull_le φ _ hj)
      (axisTorus_mem_centralizer Axis.one hj))
  have hJ2 : ∀ j ∈ 𝐉[Axis.two], j * z = z * j := by
    intro j hj
    have hjL : j ∈ L := pull_le φ _ hj
    have hjc := axisTorus_mem_centralizer Axis.two hj
    have hj'L : u * j * u⁻¹ ∈ L := (mem_normalizer_iff.mp huL j).mp hjL
    have hj'c : u * j * u⁻¹ ∈ centralizer (𝐔[Axis.one] : Set G) := by
      refine mem_centralizer_iff.mpr fun x hx => ?_
      rw [← hUmap] at hx
      obtain ⟨x', hx', rfl⟩ := hx
      have hc := mem_centralizer_iff.mp hjc x' hx'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc u * x' * u⁻¹ * (u * j * u⁻¹) = u * (x' * j) * u⁻¹ := by group
        _ = u * (j * x') * u⁻¹ := by rw [hc]
        _ = u * j * u⁻¹ * (u * x' * u⁻¹) := by group
    have hj'N := mem_preBar_of_centralizer h hbt hj'L hj'c
    have hpX : (u * u)⁻¹ ∈ normalizer (𝐗[Axis.one] : Set G) :=
      inv_mem (S_le_normalizer_X h hbt Axis.one hu2)
    have hnN := preBar_conj (Nb := normalClosure (𝐊[Axis.one] : Set (BarM 𝐗[Axis.one])))
      hpX hj'N
    have := hz2 _ hnN
    rwa [show u * ((u * u)⁻¹ * (u * j * u⁻¹) * (u * u)⁻¹⁻¹) * u⁻¹ = j by group] at this
  have hz : z ∈ 𝐖[Axis.one] ⊓ 𝐖[Axis.one.swap] :=
    ⟨⟨hzF, mem_centralizer_iff.mpr fun j hj => hJ1 j hj⟩,
      ⟨hzF, mem_centralizer_iff.mpr fun j hj => hJ2 j hj⟩⟩
  rw [RootStandard.W_inf_W_swap_eq h Axis.one] at hz
  exact mem_bot.mp hz

theorem false_of_swap (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    {α : 𝐊[Axis.one] ≃* SL(2, K)}
    (hex : ExactClosure 𝐊[Axis.one] α
      (barMap 𝐗[Axis.one] ⟨t, t_mem_normalizer_X h Axis.one⟩) (barSub 𝐗[Axis.one] 𝐒) n)
    (hF : FieldAlternative 𝐊[Axis.one]
      (barMap 𝐗[Axis.one] ⟨t, t_mem_normalizer_X h Axis.one⟩) n)
    {u : G} (huC : u ∈ 𝐂) (huT : u ∈ normalizer (𝐓₀ : Set G))
    (hU : ∀ x ∈ 𝐔[Axis.two], u * x * u⁻¹ ∈ 𝐔[Axis.one]) (huu : u * u ∈ 𝐏) : False := by
  obtain ⟨-, -, hSN, hSyl, -⟩ := hex
  obtain ⟨k₂, _, _, hk₂, ψ, -, -⟩ := hF
  have hn2 : 2 ≤ n := h.setup.two_le
  have hk₂' : Nat.card k₂ = 2 ^ (2 * n) := by
    rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, mul_comm]
  haveI : CharP k₂ 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hk₂'
  obtain ⟨π, hπs, hπk, hπS⟩ := exists_preBarHom hk₂' (X_le_S Axis.one) ψ hSyl
  have hPS : 𝐏 ≤ 𝐒 := by
    rw [← BothTrivialSlice.S_inf_C h hbt]
    exact inf_le_left
  have hu2 : u * u ∈ 𝐒 := hPS huu
  have huQ : u ∈ normalizer (𝐐 : Set G) := centralizer_inf_normalizer_le h hbt ⟨huC, huT⟩
  have huS : u ∈ normalizer (𝐒 : Set G) := normalizer_Q_le_normalizer_S h hbt huQ
  obtain ⟨hX₁, hX₂⟩ := map_X_swap h hbt huC huT hU
  exact Data.impossible (G := G) (k := k₂) (m := 2 * n)
    { S := 𝐒
      X₁ := 𝐗[Axis.one]
      X₂ := 𝐗[Axis.two]
      F := 𝐅
      N := 𝐍
      w := 𝐰[Axis.one]
      u := u
      π := π
      hk := hk₂'
      hm := by omega
      hm3 := by omega
      hm2 := three_dvd_two_pow_two_mul n
      X₁_le := X_le_S Axis.one
      X₂_le := X_le_S Axis.two
      S_eq := S_eq_aux h hbt
      X₁_ab := fun a ha b hb =>
        comm_of_mul_self (S := 𝐗[Axis.one]) (fun _ hy => X_mul_self h hbt Axis.one hy) ha hb
      X₂_ab := fun a ha b hb =>
        comm_of_mul_self (S := 𝐗[Axis.two]) (fun _ hy => X_mul_self h hbt Axis.two hy) ha hb
      X₁_sq := fun x hx => X_mul_self h hbt Axis.one hx
      X₂_sq := fun x hx => X_mul_self h hbt Axis.two hx
      F_le₁ := le_sup_left
      F_le₂ := le_sup_left
      X₁_inf_X₂ := fun x h1 h2 => (X_inf_X h).le ⟨h1, h2⟩
      F_central := fun f hf s hs => F_comm_S h hbt hf hs
      centre_le := centre_le_aux h hbt
      comm_mem_F := fun s hs s' hs' => commutator_mem h hbt hs hs'
      card_X₁ := card_X_aux h Axis.one
      card_F := card_F_aux h
      S_le_N := fun s hs => S_le_N_aux h hbt hSN hs
      N_le_norm := preBar_le_normalizer
      N_conj := fun g hg n hn => preBar_conj hg hn
      π_surj := hπs
      π_ker := hπk
      π_S := hπS
      w_mem := w_mem_aux h hbt
      X₁_eq := X₁_eq_aux h
      u_norm := huS
      u_X₁ := fun x hx => hX₁ ▸ ⟨x, hx, rfl⟩
      u_X₂ := fun x hx => hX₂ ▸ ⟨x, hx, rfl⟩
      u_sq := hu2
      CC := cc_aux h hbt huC hU hu2 }

end Setting

end BothTrivialTwistConcrete

end CFSG.LocalAnalysis.EvenBN.Sp4
