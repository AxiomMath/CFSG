module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4FamOf
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvSym
public import Certificates.Certificate5156
public import Certificates.Certificate5150
public import CFSG.GH74.Generic.S45.LEvSporM12Spec

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.ComponentClassification.M12Cover
  CFSG.GH74.Generic.S45 CFSG.GH74.Generic.S45.EvSpor
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped commutatorElement

theorem m12_C2B_enums
    (h : enumOK 24 cap Certificates.IvkCent.m12Q2Gens 384 = true) :
    EnumsSub 24 Certificates.IvkCent.m12C2B (autModel ⊓ Subgroup.centralizer ({m12A1} : Set (Equiv.Perm (Fin 24)))) := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hE, -, hrep⟩ := enumOK_spec hn h
  have himg := tp_image_toTable hn q2Gens hrep
  have hQ := (q2Q_spec).1
  have : q2Q.originalSubgroup = Subgroup.closure {g | g ∈ q2Gens} := by
    rw [q2Q, certificate_originalSubgroup]
  have hE' : EnumsSub 24 Certificates.IvkCent.m12C2B
      (Subgroup.closure (tp 24 '' {x | x ∈ (q2Gens.map toTable).toArray})) := hE
  rw [himg, ← this, hQ] at hE'
  exact hE'

theorem m12_cent_Ka :
    ∀ x ∈ autModel,
      (∀ a ∈ Subgroup.closure (tp 24 '' {x | x ∈ m12KaGens.toArray}), x * a = a * x) →
      x = 1 ∨ x = blockHom (permZ, permZ) ∨ x = m12Sigma ∨ x = m12Sigma * blockHom (permZ, permZ) := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hC2A, hKa, -, -⟩ := Certificates.certificate5150
  obtain ⟨-, -, -, hKrep⟩ := m12_Ka_facts hC2A hKa
  have h56 := Certificates.certificate5156
  simp only [Certificates.IvkCent.m12CentKaOK, Bool.and_eq_true] at h56
  obtain ⟨⟨hen, hinv⟩, hall⟩ := h56
  have hEC := m12_C2B_enums hen
  intro x hxW hxc
  have hKaB : m12KaB ∈ m12KaGens := by simp [m12KaGens]
  have hA1 : m12AT ∈ m12KaGens := by simp [m12KaGens]
  have hrepKaB : Rep 24 m12KaB (tp 24 m12KaB) := hKrep _ hKaB
  have hrepA1 : Rep 24 m12AT (tp 24 m12AT) := hKrep _ hA1
  have hmemKaB : tp 24 m12KaB ∈ Subgroup.closure (tp 24 '' {x | x ∈ m12KaGens.toArray}) :=
    Subgroup.subset_closure ⟨m12KaB, List.mem_toArray.2 hKaB, rfl⟩
  have hmemA1 : tp 24 m12AT ∈ Subgroup.closure (tp 24 '' {x | x ∈ m12KaGens.toArray}) :=
    Subgroup.subset_closure ⟨m12AT, List.mem_toArray.2 hA1, rfl⟩
  have hA1eq : tp 24 m12AT = m12A1 := rep_unique hrepA1 (rep_toTable hn _)
  have hxA1 : x ∈ autModel ⊓ Subgroup.centralizer ({m12A1} : Set (Equiv.Perm (Fin 24))) := by
    refine Subgroup.mem_inf.2 ⟨hxW, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hA1eq]
    exact hxc _ hmemA1
  obtain ⟨T, hT, hTx⟩ := hEC.rep_mem hxA1
  rw [Array.all_eq_true_iff_forall_mem] at hall
  have h1 := hall T hT
  have hcomm : commTT 24 T m12KaB = true := (commTT_iff hTx hrepKaB).2 (hxc _ hmemKaB)
  rw [hcomm] at h1
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at h1
  have hZ : Rep 24 m12ZT (blockHom (permZ, permZ)) := rep_toTable hn _
  have hS : Rep 24 m12ST m12Sigma := rep_toTable hn _
  rcases h1 with ((h1 | h1) | h1) | h1
  · exact Or.inl ((tblEq_iff_eq hTx (Rep.idT hn)).1 h1)
  · exact Or.inr (Or.inl ((tblEq_iff_eq hTx hZ).1 h1))
  · exact Or.inr (Or.inr (Or.inl ((tblEq_iff_eq hTx hS).1 h1)))
  · exact Or.inr (Or.inr (Or.inr ((tblEq_iff_eq hTx (Rep.compT hS hZ)).1 h1)))


theorem card_subgroup_le_of_forall_mem {G : Type*} [Group G] (S : Subgroup G) (F : Finset G)
    (h : ∀ s ∈ S, s ∈ F) : Nat.card ↥S ≤ F.card := by
  calc Nat.card ↥S ≤ Nat.card ↥(F : Set G) :=
        Nat.card_le_card_of_injective (fun s : ↥S => (⟨s.1, h s.1 s.2⟩ : ↥(F : Set G)))
          (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
    _ = F.card := Nat.card_eq_finsetCard F

theorem card_centralizerIn_of_outer {G : Type*} [Group G] [Finite G] {N H : Subgroup G}
    (hHN : H ≤ N) (hcard : Nat.card ↥N = 2 * Nat.card ↥H) {t v : G} (hv : v ∈ N) (hvH : v ∉ H)
    (hvt : v * t = t * v) :
    Nat.card ↥(centralizerIn N t) = 2 * Nat.card ↥(centralizerIn H t) := by
  have h := card_cent_of_outer hHN hcard hv hvH hvt
  have e1 : centralizerIn N t = Subgroup.centralizer ({t} : Set G) ⊓ N := inf_comm _ _
  have e2 : centralizerIn H t = Subgroup.centralizer ({t} : Set G) ⊓ H := inf_comm _ _
  rw [e1, e2]
  exact h

theorem m12_model :
    Ivk73Model blockGroup autModel (Subgroup.closure (tp 24 '' {x | x ∈ m12KaGens.toArray}))
      (blockHom (permZ, permZ)) := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨-, -, -, -, -, -, -, -, -, hreps, hC2A, hKa, hder, hout⟩ :=
    Certificates.certificate5150
  obtain ⟨hEC, hinv⟩ := m12_C2A_enums hC2A
  obtain ⟨hEK, hKcard, hKW, hKrep⟩ := m12_Ka_facts hC2A hKa
  simp only [m12RepsOK, Bool.and_eq_true] at hreps
  obtain ⟨⟨⟨⟨⟨-, hZi⟩, -⟩, hAi⟩, -⟩, hSi⟩ := hreps
  have hZo : orderOf (blockHom (permZ, permZ)) = 2 :=
    orderOf_eq_two_of_involOK hn (rep_toTable hn _) hZi
  have hZD : blockHom (permZ, permZ) ∈ blockGroup := by
    rw [← m12EquivD_elemZ]
    exact (m12EquivD elemZ).2
  simp only [m12OuterOK, Bool.and_eq_true] at hout
  obtain ⟨⟨hoZ, hoA⟩, hoK⟩ := hout
  have hσrep : Rep 24 m12ST m12Sigma := rep_toTable hn _
  have hσZ : m12Sigma * blockHom (permZ, permZ) = blockHom (permZ, permZ) * m12Sigma :=
    (commTT_iff hσrep (rep_toTable hn _)).1 hoZ
  have hσA : m12Sigma * m12A1 = m12A1 * m12Sigma :=
    (commTT_iff hσrep (rep_toTable hn _)).1 hoA
  have hcardW : Nat.card autModel = 2 * Nat.card blockGroup := card_autModel_eq
  have hautM := m12_smallAutModel
  have hnormW : ∀ x ∈ autModel, ∀ p ∈ blockGroup, x * p * x⁻¹ ∈ blockGroup := hautM.conj_mem
  have hnormW' : ∀ x ∈ autModel, ∀ p ∈ blockGroup, x⁻¹ * p * x ∈ blockGroup := fun x hx p hp => by
    simpa using hnormW x⁻¹ (autModel.inv_mem hx) p hp
  have hcentZ : Nat.card ↥(centralizerIn blockGroup (blockHom (permZ, permZ))) = 240 := by
    have h480 : Nat.card ↥(centralizerIn autModel (blockHom (permZ, permZ))) = 480 := by
      have h := q4Q_spec
      rw [← h.1]
      exact h.2.1
    have := card_centralizerIn_of_outer blockGroup_le_autModel hcardW sigma_mem_autModel
      sigma_not_mem_blockGroup hσZ
    omega
  have hcentA : Nat.card ↥(centralizerIn blockGroup m12A1) = 192 := by
    have h384 : Nat.card ↥(centralizerIn autModel m12A1) = 384 := by
      have h := q2Q_spec
      rw [← h.1]
      exact h.2.1
    have := card_centralizerIn_of_outer blockGroup_le_autModel hcardW sigma_mem_autModel
      sigma_not_mem_blockGroup hσA
    omega
  refine
    { autModel := hautM
      card_le := hcardW.le
      tX_mem := hZD
      tX_ord := hZo
      card_A := hKcard
      card_cent := hcentZ
      derived := ?_
      classes := ?_ }
  · intro x hx y hy
    exact innerDerived_spec (D := m12C2A) hEC hEK hinv hder
      (P := fun g => g ∈ blockGroup ∧ g ∈ Subgroup.centralizer
        ({blockHom (permZ, permZ)} : Set (Equiv.Perm (Fin 24))))
      (fun g hg => ⟨blockGroup_le_autModel hg.1, hg.2⟩)
      (fun g hg => innerT_of_mem_blockGroup hg.1) x y (Subgroup.mem_inf.1 hx) (Subgroup.mem_inf.1 hy)
  · intro t htD ht2
    obtain ⟨r, hr, c, hc, hδ⟩ := autModel_involution_cover (blockGroup_le_autModel htD) ht2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · right
      have hcardt : Nat.card ↥(centralizerIn blockGroup t) = 192 := by
        rw [hδ, GHInv.card_centralizerIn_conj_of_norm (hnormW c hc) (hnormW' c hc)]
        exact hcentA
      exact GHInv.NoU2Comp.of_solvable (GHInv.isSolvable_of_card_dvd_two_pow_mul_three_pow
        (a := 6) (b := 1) (by rw [hcardt]; norm_num))
    · exact Or.inl ⟨c, hc, hδ⟩
    · exfalso
      apply sigma_not_mem_blockGroup
      have := hnormW' c hc t htD
      rw [hδ] at this
      simpa [mul_assoc] using this

theorem m12_tZ_mem :
    blockHom (permZ, permZ) ∈ blockGroup := by
  rw [← m12EquivD_elemZ]
  exact (m12EquivD elemZ).2

theorem ivk73_m12 :
    Ivk73Fam (fun X _ => NativeSporadic.IsSporadic X .M12) := by
  intro N _ _ L K Q h hL
  obtain ⟨e⟩ := hL
  have e' : ↥L ≃* NativeSporadic.M12 := e
  let θ : ↥L ≃* ↥blockGroup := e'.trans m12EquivD
  have hKa5 := m12_cent_Ka
  have hZD := m12_tZ_mem
  obtain ⟨hcardN, hKbar, hb1, hb2⟩ := h.of_model m12_model θ (b₁ := 4) (b₂ := 2)
    (fun S hSW hSc _ => by
      refine (card_subgroup_le_of_forall_mem S
        {1, blockHom (permZ, permZ), m12Sigma, m12Sigma * blockHom (permZ, permZ)} ?_).trans
        Finset.card_le_four
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hKa5 s (hSW hs) (fun a ha => hSc a ha s hs) with h1 | h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr h1)))
    (fun S hSP hSc => by
      refine (card_subgroup_le_of_forall_mem S {1, blockHom (permZ, permZ)} ?_).trans
        Finset.card_le_two
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hKa5 s (blockGroup_le_autModel (hSP hs)) (fun a ha => hSc a ha s hs) with
        h1 | h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exact absurd (h1 ▸ hSP hs) sigma_not_mem_blockGroup
      · exfalso
        have hs' : m12Sigma * blockHom (permZ, permZ) ∈ blockGroup := h1 ▸ hSP hs
        apply sigma_not_mem_blockGroup
        have := blockGroup.mul_mem hs' (blockGroup.inv_mem hZD)
        simpa using this)
  obtain ⟨hQel, hQ4⟩ := h.Q_row hb1
  have hNL : L ≠ ⊤ := by
    intro hLtop
    have hle : Q ≤ centralizer (K : Set N) ⊓ L := le_inf h.Q_sylow.le (hLtop ▸ le_top)
    have := Subgroup.card_le_of_le hle
    omega
  rcases h.index_row hcardN with hLtop | hN2
  · exact absurd hLtop hNL
  · exact ⟨hQel, hQ4, Or.inl ⟨hKbar, ⟨e⟩, hN2⟩⟩

end CFSG.GH74.GLS.IVK
