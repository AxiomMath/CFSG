module

public import CFSG.ClassicalInvolution.Q3.TL3T12_6E29Ker
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3Cent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfClosureE29
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfMembers

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

variable {G : Type} [Group G] [Finite G]

theorem noCentralInv_of_e29 {P : Set (Subgroup G)} (I : AEIdentOn P 8 AE.e29Sets AE.e29Sub)
    (hc8 : ∀ L ∈ P, Nat.card L = 8) : NoCentralInv P := by
  intro L hL u hu hc
  obtain ⟨α, hα, h4, b, hlab⟩ := I.label L hL
  set uS : ↥(pSpan P) := ⟨u, le_pSpan hL hu.mem⟩ with huS
  have hZ : Subgroup.center ↥I.φ.range = ⊥ := by
    rw [I.range_eq]
    exact TwinThinPf.center_e29_eq_bot
  have hcS : ∀ y : ↥(pSpan P), y * uS = uS * y := fun y => Subtype.ext (hc y y.2)
  have hmem : (⟨I.φ uS, uS, rfl⟩ : ↥I.φ.range) ∈ Subgroup.center ↥I.φ.range := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨_, y, rfl⟩
    apply Subtype.ext
    show I.φ y * I.φ uS = I.φ uS * I.φ y
    rw [← map_mul, ← map_mul, hcS y]
  rw [hZ, Subgroup.mem_bot] at hmem
  have h1 : I.φ uS = I.φ ⟨1, le_pSpan hL L.one_mem⟩ := by
    have := congrArg Subtype.val hmem
    have e : (⟨1, le_pSpan hL L.one_mem⟩ : ↥(pSpan P)) = 1 := rfl
    rw [e, map_one]
    exact this
  exact hu.ne_one (phi_injOn I.φ (by norm_num) hL (hc8 L hL) hlab hu.mem L.one_mem h1)

section NoTwins

variable {r : ℕ} {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

theorem CHyp.thinStd_of_noTwins {K J : Subgroup G} (hS : CHyp r IH Ω K J)
    (h8 : ∀ L ∈ Ω, Nat.card L = 8)
    (htw : ∀ J₁ ∈ Ω, ∀ J₂ ∈ Ω, ∀ w : G, IsUniqueInvolution J₁ w → IsUniqueInvolution J₂ w →
      J₁ = J₂) : ThinStd Ω K where
  hyp := hS.hyp
  two := hS.two
  card := h8
  tight := fun L hL u hu c hc => by
    have hcu : c * u = u * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hcu' : c * u * c⁻¹ = u := by rw [hcu]; group
    have h1 : IsUniqueInvolution (conjSub c L) u := by
      have := hu.conj c
      rwa [hcu'] at this
    exact mem_normalizer_of_conjSub_eq (htw _ (hS.hyp.conjInvariant c L hL) L hL u h1 hu)
  aEmpty := hS.aEmpty
  mem := hS.adj.1
  trans := fun L hL => hS.trans K hS.adj.1 L hL
  gen := hS.gen
  conn := hS.conn
  sep := hS.toCHypG.sepHyp

theorem CHyp.false_of_e29_of_noTwins {K J : Subgroup G} (hS : CHyp 3 IH Ω K J)
    (htw : ∀ J₁ ∈ Ω, ∀ J₂ ∈ Ω, ∀ w : G, IsUniqueInvolution J₁ w → IsUniqueInvolution J₂ w →
      J₁ = J₂)
    (I : AEIdentOn (orbOf (TC.nbrAdj Ω) K J) 8 AE.e29Sets AE.e29Sub) : False := by
  have hc8 : ∀ L ∈ Ω, Nat.card L = 8 := fun L hL => by rw [hS.card L hL]; norm_num
  have hSt : ThinStd Ω K := hS.thinStd_of_noTwins hc8 htw
  have hK : K ∈ Ω := hS.adj.1
  have hJ : J ∈ Ω := hS.adj.2.1
  have hN : MaxAdj (TC.nbrAdj Ω) K J := ⟨hS.adj, hS.max⟩
  have hNK : MaxAdj (TC.nbrAdj Ω) J K := ⟨hS.swap.adj, hS.swap.max⟩
  obtain ⟨g, hg⟩ := hS.trans K hK J hJ
  have eK : {L : Subgroup G | MaxAdj (TC.nbrAdj Ω) K L} = orbOf (TC.nbrAdj Ω) K J :=
    Set.ext fun L => hSt.maxAdj_iff_mem_orbOf hN
  have eJ : {L : Subgroup G | MaxAdj (TC.nbrAdj Ω) J L} = orbOf (TC.nbrAdj Ω) J K :=
    Set.ext fun L => hSt.maxAdj_iff_mem_orbOf hNK
  have IM : AEIdentOn {L : Subgroup G | MaxAdj (TC.nbrAdj Ω) K L} 8 AE.e29Sets AE.e29Sub :=
    AEIdentOn.ofEq eK.symm I
  have IN : AEIdentOn {L : Subgroup G | MaxAdj (TC.nbrAdj Ω) J L} 8 AE.e29Sets AE.e29Sub :=
    AEIdentOn.ofEq eJ.symm (AEIdentOn.ofEq (hS.orb_swap_eq hg) (I.conj g))
  exact hSt.false_of_e29 hS.center hN IM IN

end NoTwins

theorem cLeafE29G_proved (IH : ℕ → Prop) :
    CLeafE29G 3 IH := by
  intro G _ _ Ω K J hS ⟨I⟩
  by_cases htw : ∀ J₁ ∈ Ω, ∀ J₂ ∈ Ω, ∀ w : G, IsUniqueInvolution J₁ w →
      IsUniqueInvolution J₂ w → J₁ = J₂
  · exact hS.false_of_e29_of_noTwins htw I
  push Not at htw
  obtain ⟨J₁, hJ₁, J₂, hJ₂, w, hw₁, hw₂, hne₁₂⟩ := htw
  have hK : K ∈ Ω := hS.adj.1
  have hJ : J ∈ Ω := hS.adj.2.1
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hKπ' : K ∈ orbOf (TC.nbrAdj Ω) J K := mem_orbOf_self J K
  have hP : SecHyp 3 Ω (orbOf (TC.nbrAdj Ω) K J) := hS.secHyp
  have hP' : SecHyp 3 Ω (orbOf (TC.nbrAdj Ω) J K) := hS.swap.secHyp
  have hc8 : ∀ L ∈ Ω, Nat.card L = 8 := fun L hL => by rw [hS.card L hL]; norm_num
  have hH1 : NoCentralInv (orbOf (TC.nbrAdj Ω) K J) :=
    noCentralInv_of_e29 I fun L hL => hc8 L (hP.sub hL)
  obtain ⟨⟨z, hz⟩, -⟩ := hS.hyp.omega1 K hK
  obtain ⟨g, hg⟩ := hS.trans K hK J hJ
  let I' : AEIdentOn (orbOf (TC.nbrAdj Ω) J K) 8 AE.e29Sets AE.e29Sub :=
    AEIdentOn.ofEq (hS.orb_swap_eq hg) (I.conj g)
  have hk2 : IsPGroup 2 I'.φ.ker := I'.toLabel.isPGroup_ker hP'.odd
  have hc8' : ∀ L ∈ orbOf (TC.nbrAdj Ω) J K, Nat.card L = 8 := fun L hL => hc8 L (hP'.sub hL)
  have hH1' : NoCentralInv (orbOf (TC.nbrAdj Ω) J K) := noCentralInv_of_e29 I' hc8'
  obtain ⟨c, hc⟩ := hS.trans J₁ hJ₁ J hJ
  have hu : IsUniqueInvolution J (c * w * c⁻¹) := by
    have := hw₁.conj c
    rwa [hc] at this
  have hu'' : IsUniqueInvolution (conjSub c J₂) (c * w * c⁻¹) := hw₂.conj c
  have hJ''Ω : conjSub c J₂ ∈ Ω := hS.hyp.conjInvariant c J₂ hJ₂
  have hne'' : conjSub c J₂ ≠ J := by
    intro h
    exact hne₁₂ (conjSub_injective c (h.trans hc.symm)).symm
  have hβ : conjSub c J₂ ∈ betaOf (TC.nbrAdj Ω) Ω (orbOf (TC.nbrAdj Ω) J K) :=
    hS.orbitStd.twinSet_subset_beta hS.swap.max hH1'
      (show conjSub c J₂ ∈ twinSet Ω J from ⟨hJ''Ω, c * w * c⁻¹, hu, hu''⟩)
  have hJ''π : conjSub c J₂ ∈ orbOf (TC.nbrAdj Ω) K J := by
    have hKJ : conjSub g⁻¹ J = K := by rw [← hg, conjSub_inv_conjSub]
    have hKg : conjSub g⁻¹ J ∈ orbOf (TC.nbrAdj Ω) J K := by rw [hKJ]; exact hKπ'
    obtain ⟨M, hM, hMe⟩ := hS.orbitStd.beta_subset_conj_image hJ hS.swap.max hKg hβ
    rw [← hS.orb_swap_eq hg] at hM
    obtain ⟨M', hM', rfl⟩ := hM
    rw [conjSub_inv_conjSub] at hMe
    rwa [← hMe]
  have hJ''cent : ∀ y ∈ pSpan (orbOf (TC.nbrAdj Ω) J K), ∀ l ∈ conjSub c J₂,
      y * l = l * y := fun y hy l hl =>
    Subgroup.mem_centralizer_iff.mp (hS.orbitStd.beta_le_centralizer hβ hl) y hy
  have hne_img : (J.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ ≠
      ((conjSub c J₂).subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ := by
    intro he
    obtain ⟨α, -, h4, b, hlab⟩ := I.label J hJπ
    exact hne'' (TL4.eq_of_map_le_memBar hS.hyp hS.two (by norm_num) I.φ
      (I.toLabel.isPGroup_ker hP.odd) (hP.sub hJ''π) (hP.sub hJπ) (le_pSpan hJ''π)
      (le_pSpan hJπ) (he.symm.trans hlab) he.symm.le)
  have hStepA : ∀ y ∈ pSpan (orbOf (TC.nbrAdj Ω) J K), y * z = z * y →
      (∃ a : ℕ, y ^ 3 ^ a = 1) → ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), y * x = x * y := by
    intro y hy hyz hy3
    have hyN := hS.centralizer_le_normalizer_orb hH1 hz
      (Subgroup.mem_centralizer_singleton_iff.mpr hyz)
    have hyJ : ∀ l ∈ J, y * l = l * y := fun l hl =>
      ((Subgroup.mem_centralizer_iff.mp (hS.pSpan_swap_le_centralizer hy)) l hl).symm
    exact TwinThinPf.centralizes_of_e29_pair I hyN hy3 hJπ hJ''π (hc8 J hJ)
      (hc8 _ hJ''Ω) hu hu'' hne_img hyJ (hJ''cent y hy) (fun L' hL' => hP.trans J hJπ L' hL')
  have hinj' : ∀ L ∈ orbOf (TC.nbrAdj Ω) J K, ∀ L' ∈ orbOf (TC.nbrAdj Ω) J K,
      (L.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) J K))).map I'.φ =
        (L'.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) J K))).map I'.φ → L = L' := by
    intro L hL L' hL' he
    obtain ⟨α, -, h4, b, hlab⟩ := I'.label L hL
    exact TL4.eq_of_map_le_memBar hS.hyp hS.two (by norm_num) I'.φ hk2 (hP'.sub hL)
      (hP'.sub hL') (le_pSpan hL) (le_pSpan hL') hlab he.le
  have hker := AEIdentOn.ker_le_threeClosure_e29 I' hP'.odd hc8' hP'.inv hinj' hKπ' hz
  refine hS.false_of_cent hH1 fun L hL u hu x hx => ?_
  obtain ⟨t, htT, htk⟩ := TwinThinPf.exists_mem_threeClosure (by norm_num) I'
    TwinThinPf.oddClosure_e29 hP'.odd hc8' hKπ' hz hL hu
  have huT : (⟨u, le_pSpan hL hu.mem⟩ : ↥(pSpan (orbOf (TC.nbrAdj Ω) J K))) ∈
      Subgroup.closure (TwinThinPf.threeGens (orbOf (TC.nbrAdj Ω) J K)
        (⟨z, le_pSpan hKπ' hz.mem⟩ : ↥(pSpan (orbOf (TC.nbrAdj Ω) J K)))) := by
    have := Subgroup.mul_mem _ htT (hker _ htk)
    simpa using this
  have hle : Subgroup.closure (TwinThinPf.threeGens (orbOf (TC.nbrAdj Ω) J K)
      (⟨z, le_pSpan hKπ' hz.mem⟩ : ↥(pSpan (orbOf (TC.nbrAdj Ω) J K)))) ≤
      (Subgroup.centralizer ((pSpan (orbOf (TC.nbrAdj Ω) K J) : Subgroup G) : Set G)).comap
        (pSpan (orbOf (TC.nbrAdj Ω) J K)).subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro w ⟨hwz, a, hwa⟩ x hx
    have hwz' : (w : G) * z = z * (w : G) := congrArg Subtype.val hwz
    have hw3 : ∃ a : ℕ, (w : G) ^ 3 ^ a = 1 :=
      ⟨a, by simpa using congrArg Subtype.val hwa⟩
    exact (hStepA w w.2 hwz' hw3 x hx).symm
  exact Subgroup.mem_centralizer_iff.mp (hle huT) x hx

end CFSG.ClassicalInvolution.Q3.TC.Thin
