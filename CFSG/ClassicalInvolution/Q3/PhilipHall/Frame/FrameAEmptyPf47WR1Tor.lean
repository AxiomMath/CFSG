module

public import CFSG.ClassicalInvolution.AschTight.Sec7L98D
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64Main

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.WR1

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G]

set_option hygiene false in
local notation "𝕌𝕍" => (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G)
set_option hygiene false in
local notation "𝕏𝕏" =>
  ((J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)) : Subgroup G)
set_option hygiene false in
local notation "𝕐𝕐" => (pairNormalizers K J z j)

structure Data (Ω : Set (Subgroup G)) (K J K' W : Subgroup G) (z j u v : G)
    (R R' T : Subgroup G) : Prop where
  tor : Sec7.Tor98 Ω K J K' z j u v R R' T
  hu : Subgroup.zpowers u = K ⊓ W
  hv : Subgroup.zpowers v = J ⊓ W
  hW : W ∈ WSet Ω
  hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x
  hW2 : IsPGroup 2 W
  hφ : ∃ φ : ↥𝕐𝕐 →* DihedralGroup 6, Function.Surjective φ ∧ φ.ker = Subgroup.subgroupOf 𝕏𝕏 𝕐𝕐
  hYW : ∀ W' : Subgroup G, IsPGroup 2 W' → 𝕌𝕍 ≤ W' →
    W' ≤ Subgroup.centralizer (𝕌𝕍 : Set G) → 𝕐𝕐 ⊓ W' = 𝕌𝕍

variable [Finite G] {Ω : Set (Subgroup G)}

theorem exists_data (hΩ : HypOmegaGen Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hA : InA Ω K J) {z j : G} (hz : IsUniqueInvolution K z) (hj : IsUniqueInvolution J j) :
    ∃ (K' W : Subgroup G) (u v : G) (R R' T : Subgroup G), Data Ω K J K' W z j u v R R' T := by
  obtain ⟨-, -, -, -, Ks, -, -, -, -, -, -, -, -, -, -, -, -, -, hne, htw, -⟩ :=
    Sec6Gen.l6_4ThreeGen G Ω hΩ K hK J hJ hA z j hz hj _ _ rfl rfl
  have hKs : Ks ∈ Ω := by
    have h : Ks ∈ twinSet Ω K := by
      rw [htw]
      exact Or.inr rfl
    exact h.1
  obtain ⟨-, -, U', hU', hU'J, hU'N⟩ := hA.1
  have hU'c : U' ≤ J ⊓ Subgroup.centralizer ({z} : Set G) :=
    le_inf hU'J (Sec6Gen.le_centralizer_of_le_normalizer' hz hU'N)
  have hU'2 := Sec6Gen.isPGroup_of_mem_USet hΩ hU'
  obtain ⟨-, -, -, -, -, -, -, -, hU'4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU'
  obtain ⟨P, hP, hU'P⟩ := IsSylow2In.exists_ge hU'2
    (hU'c.trans le_sup_right : U' ≤ (K ⊔ Ks) ⊔ (J ⊓ Subgroup.centralizer ({z} : Set G)))
  obtain ⟨S, hPS⟩ := hP.2.1.exists_le_sylow
  obtain ⟨η, hη, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S
  have hW : (⨆ U ∈ η, U) ∈ WSet Ω := ⟨η, ⟨S, hη, hinv⟩, rfl⟩
  have hWS : (⨆ U ∈ η, U) ≤ (S : Subgroup G) := iSup₂_le fun U hU => (hη.1 hU).2
  have hJS : 2 < Nat.card ↥(J ⊓ (S : Subgroup G)) :=
    lt_of_lt_of_le (by omega) (Subgroup.card_le_of_le (le_inf hU'J (hU'P.trans hPS)))
  have c : Sec7.Cfg98 Ω K J Ks ⊥ P z j S (⨆ U ∈ η, U) :=
    { hΩ := hΩ, hK := hK, hJ := hJ, hA := hA, hz := hz, hj := hj, hK' := hKs, hne := hne,
      htw := htw, hX2 := IsPGroup.of_bot, hXc := bot_le, hP := hP,
      hXP := fun x hx => by rw [Subgroup.mem_bot.mp hx, conjSub_one],
      hPS := sup_le hPS bot_le, hJS := hJS, hW := hW, hWS := hWS }
  obtain ⟨u, v, T, hu, hv, tor⟩ := c.exists_tor Sec6Gen.l6_4ThreeGenAll
  obtain ⟨-, ⟨-, -, -, hφ⟩, -, -, -, hYW⟩ := Sec6Gen.l6_4ThreeGenAll G Ω hΩ K hK J hJ hA z j hz hj
    _ _ rfl rfl u v tor.hU tor.hUK tor.hV tor.hVJ tor.hcomm _ T tor.hR tor.hT tor.huR tor.hvT
    tor.hRN tor.hTN
  exact ⟨Ks, _, u, v, _, _, T, ⟨tor, hu, hv, hW, c.W_abelian, c.W_isPGroup, hφ, hYW⟩⟩

namespace Data

variable {K J K' W : Subgroup G} {z j u v : G} {R R' T : Subgroup G}
  (d : Data Ω K J K' W z j u v R R' T)
include d

theorem UV_le_W : 𝕌𝕍 ≤ W := by
  refine sup_le ?_ ?_
  · rw [d.hu]
    exact inf_le_right
  · rw [d.hv]
    exact inf_le_right

theorem z_mem_W : z ∈ W := d.UV_le_W (Subgroup.mem_sup_left d.tor.z_mem_U)

end Data

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.WR1
