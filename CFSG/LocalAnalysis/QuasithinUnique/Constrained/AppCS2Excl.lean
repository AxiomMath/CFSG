module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Cent2

public section

namespace CFSG.QuasithinUnique.AppCS2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.DoubleA3 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

namespace Two

variable {t x : G} (X : Two T M H S L t x)
include X

theorem exists_involution_over_z :
    ∃ ℓ : ↥L, ℓ * ℓ = 1 ∧ ((X.C.P.α ℓ : alternatingGroup (Fin 5)) : Perm (Fin 5)) = zA := by
  have hD := X.C.D
  have hVN : conjR (blockU L) x ≤ normalizer (L : Set G) := X.C.V_le_N X.hx
  have hzE : zA ∈ Eset := (mem_Eset_iff _).2 (Or.inr (Or.inr (Or.inr rfl)))
  have hzV : zA ∈ X.C.P.im (conjR (blockU L) x) := by
    rw [X.hVE]; exact (mem_Estd _).2 hzE
  obtain ⟨t₀, ht₀V, ht₀z⟩ := (X.C.P.mem_im_pf hVN).1 hzV
  have ht₀B : t₀ ∈ baum S := X.C.V_le_baum X.hx ht₀V
  have ht₀N : t₀ ∈ normalizer (L : Set G) := X.C.hBN ht₀B
  have ht₀2 : t₀ * t₀ = 1 := by
    have := (C5.isElemAbelian_two_iff.mp (X.C.V_elem x)).2 t₀ ht₀V
    rwa [pow_two] at this
  obtain ⟨ℓ₀, hℓ₀⟩ := X.C.P.hα ⟨zA, Equiv.Perm.mem_alternatingGroup.2 zA_sign⟩
  have hℓ₀N : (ℓ₀ : G) ∈ normalizer (L : Set G) := Subgroup.le_normalizer ℓ₀.2
  have hpℓ₀ : X.C.P.pf (ℓ₀ : G) = zA := by
    rw [X.C.P.pf_eq hℓ₀N, X.C.P.hπα (ℓ₀ : G) ℓ₀.2, hℓ₀]
  have hℓ₀inv : (ℓ₀ : G)⁻¹ ∈ normalizer (L : Set G) := (normalizer (L : Set G)).inv_mem hℓ₀N
  have hyN : (ℓ₀ : G)⁻¹ * t₀ ∈ normalizer (L : Set G) :=
    (normalizer (L : Set G)).mul_mem hℓ₀inv ht₀N
  have hypf : X.C.P.pf ((ℓ₀ : G)⁻¹ * t₀) = 1 := by
    rw [X.C.P.pf_mul hℓ₀inv ht₀N, X.C.P.pf_inv hℓ₀N, hpℓ₀, ht₀z, inv_mul_cancel]
  have hyC : ∀ u ∈ blockU L, ((ℓ₀ : G)⁻¹ * t₀) * u = u * ((ℓ₀ : G)⁻¹ * t₀) := by
    intro u hu
    have hypf' := hypf
    rw [X.C.P.pf_eq hyN] at hypf'
    have h2 := (X.C.P.hker ⟨_, hyN⟩).1 hypf' u hu
    calc ((ℓ₀ : G)⁻¹ * t₀) * u = (((ℓ₀ : G)⁻¹ * t₀) * u * ((ℓ₀ : G)⁻¹ * t₀)⁻¹) *
          ((ℓ₀ : G)⁻¹ * t₀) := by group
      _ = u * ((ℓ₀ : G)⁻¹ * t₀) := by rw [h2]
  have hyX : (ℓ₀ : G)⁻¹ * t₀ ∈ (L ⊔ baum S) ⊓ centralizer (blockU L : Set G) :=
    Subgroup.mem_inf.2 ⟨(L ⊔ baum S).mul_mem ((L ⊔ baum S).inv_mem (Subgroup.mem_sup_left ℓ₀.2))
      (Subgroup.mem_sup_right ht₀B), Subgroup.mem_centralizer_iff.2 fun u hu => (hyC u hu).symm⟩
  rw [hD.Q1_inf_centralizer] at hyX
  obtain ⟨u, hu, d, hd, hud⟩ := X.C.Q1_decomp hyX
  have huL : u ∈ L := hD.blockU_le_L hu
  have hd_eq : d = u⁻¹ * ((ℓ₀ : G)⁻¹ * t₀) := by rw [← hud]; group
  have hdU₂ : ∀ b ∈ blockU2 L t, b * d = d * b := by
    intro b hb
    have hb₂ : b ∈ conjR L t := hD.blockU2_le_L₂ hb
    have c1 : Commute b u⁻¹ :=
      (show Commute b u from (hD.comm_elem u huL b hb₂).symm).inv_right
    have c2 : Commute b (ℓ₀ : G)⁻¹ :=
      (show Commute b (ℓ₀ : G) from (hD.comm_elem ℓ₀ ℓ₀.2 b hb₂).symm).inv_right
    have c3 : Commute b t₀ := (X.V₁_comm_U₂ ht₀V hb).symm
    rw [hd_eq]
    exact (c1.mul_right (c2.mul_right c3)).eq
  have hdQ₂ : d ∈ pCoreOf 2 (conjR L t ⊔ baum S) := by
    rw [X.Q₂_eq_inf]
    exact Subgroup.mem_inf.2 ⟨hd.1, Subgroup.mem_centralizer_iff.2 fun b hb => hdU₂ b hb⟩
  obtain ⟨u₂, hu₂, d₂, hd₂, hud₂⟩ := X.Q₂_decomp hdQ₂
  have hd₂D : d₂ ∈ blockD S L := by
    have h1 : d₂ ∈ s2I S L := by
      have : d₂ = u₂⁻¹ * d := by rw [← hud₂]; group
      rw [this]
      exact (s2I S L).mul_mem ((s2I S L).inv_mem (X.U₂_le_D₁ hu₂)) hd
    have h2 : d₂ ∈ baumD S L := by rw [X.baumD_eq]; exact Subgroup.mem_inf.2 ⟨h1, hd₂⟩
    rwa [X.baumD_eq_blockD] at h2
  have hd₂2 : d₂ * d₂ = 1 := by
    have := (C5.isElemAbelian_two_iff.mp X.blockD_isElemAbelian).2 d₂ hd₂D
    rwa [pow_two] at this
  have hu₂2 : u₂ * u₂ = 1 := by
    have := (C5.isElemAbelian_two_iff.mp hD.U0_isElemAbelian).2 u₂ (Subgroup.mem_sup_right hu₂)
    rwa [pow_two] at this
  have hcomm₂ : u₂ * d₂ = d₂ * u₂ := X.U0_comm_blockD hd₂D (Subgroup.mem_sup_right hu₂)
  have hdd : d * d = 1 := by
    rw [← hud₂]
    calc u₂ * d₂ * (u₂ * d₂) = u₂ * (d₂ * u₂) * d₂ := by group
      _ = u₂ * (u₂ * d₂) * d₂ := by rw [hcomm₂]
      _ = (u₂ * u₂) * (d₂ * d₂) := by group
      _ = 1 := by rw [hu₂2, hd₂2, one_mul]
  refine ⟨ℓ₀ * ⟨u, huL⟩, ?_, ?_⟩
  · apply Subtype.ext
    show ((ℓ₀ : G) * u) * ((ℓ₀ : G) * u) = 1
    set ℓ : G := (ℓ₀ : G) * u with hℓdef
    have htd : t₀ = ℓ * d := by
      calc t₀ = (ℓ₀ : G) * ((ℓ₀ : G)⁻¹ * t₀) := by group
        _ = (ℓ₀ : G) * (u * d) := by rw [hud]
        _ = ℓ * d := by rw [hℓdef]; group
    have hdc : d * ℓ = ℓ * d :=
      (Subgroup.mem_centralizer_iff.1 hd.2 ℓ (L.mul_mem ℓ₀.2 huL)).symm
    calc ℓ * ℓ = ℓ * ℓ * (d * d) := by rw [hdd, mul_one]
      _ = ℓ * (ℓ * d) * d := by group
      _ = ℓ * (d * ℓ) * d := by rw [hdc]
      _ = (ℓ * d) * (ℓ * d) := by group
      _ = t₀ * t₀ := by rw [← htd]
      _ = 1 := ht₀2
  · have hu' : (⟨u, huL⟩ : ↥L) ∈ X.C.P.α.ker := by
      rw [X.C.P.hαk]
      exact (mem_pCore_iff_mem_blockQ _).2 (C1.blockU_le_blockQ hD.hL hu)
    rw [map_mul, MonoidHom.mem_ker.1 hu', mul_one, hℓ₀]

theorem blockQ_eq_blockU : blockQ L = blockU L := by
  have hD := X.C.D
  refine le_antisymm ?_ (C1.blockU_le_blockQ hD.hL)
  obtain ⟨ℓ, hℓ, hαℓ⟩ := X.exists_involution_over_z
  have hUL : blockU L ≤ L := hD.blockU_le_L
  have hN : ((blockU L).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUL).mpr (C1.le_normalizer_blockU L)
  have hmem : ∀ q ∈ X.C.P.α.ker, (q : G) ∈ blockQ L := fun q hq => by
    rw [X.C.P.hαk] at hq
    exact (mem_pCore_iff_mem_blockQ q).1 hq
  have key := central_cover_trivial (Λ := ↥L) hD.hL.1 X.C.P.α X.C.P.hα ((blockU L).subgroupOf L)
    (fun u hu => by
      rw [MonoidHom.mem_ker]
      have hu' : u ∈ X.C.P.α.ker := by
        rw [X.C.P.hαk]
        exact (mem_pCore_iff_mem_blockQ u).2
          (C1.blockU_le_blockQ hD.hL (Subgroup.mem_subgroupOf.1 hu))
      exact hu')
    (fun q hq => by
      have hqP : (q : G) ∈ pCoreOf 2 H :=
        (C56.pCoreOf_conjJoin_le hD.hcs) (C56.blockQ_le_pCoreOf_conjJoin hD.hcs (hmem q hq))
      apply Subtype.ext
      have := (C5.isElemAbelian_two_iff.mp X.pCoreOf_isElemAbelian).2 (q : G) hqP
      simpa [pow_two] using this)
    (fun q hq g => Subgroup.mem_subgroupOf.2 (C1.commutator_mem_blockU (hmem q hq) g.2))
    ℓ hℓ hαℓ
  intro q hq
  have hqL : q ∈ L := C1.blockQ_le L hq
  have hk : (⟨q, hqL⟩ : ↥L) ∈ X.C.P.α.ker := by
    rw [X.C.P.hαk]
    exact (mem_pCore_iff_mem_blockQ _).2 hq
  exact Subgroup.mem_subgroupOf.1 (key hk)

theorem pCoreOf_conjJoin_le_Q :
    pCoreOf 2 (conjJoin S L) ≤ blockQ L ⊔ blockQ (conjR L t) := by
  have hD := X.C.D
  intro q hq
  have hqK : q ∈ conjJoin S L := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _ hq
  have hNn : ∀ g ∈ conjJoin S L,
      g ∈ normalizer ((pCoreOf 2 (conjJoin S L) : Subgroup G) : Set G) :=
    fun g hg => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (conjJoin S L)
      (Subgroup.le_normalizer hg)
  have hLK : L ≤ conjJoin S L := C56.le_conjJoin L S.one_mem
  have hL₂K : conjR L t ≤ conjJoin S L := hD.L₂_le_K
  have hLn : L ≤ normalizer ((conjR L t : Subgroup G) : Set G) :=
    C5.le_normalizer_of_commute (fun u hu a ha => hD.comm_elem u hu a ha)
  have hq' : q ∈ ((L ⊔ conjR L t : Subgroup G) : Set G) := by
    rw [← hD.hjoin]; exact hqK
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L (conjR L t) hLn] at hq'
  obtain ⟨a, ha, b, hb, hab⟩ := hq'
  have hab' : a * b = q := hab
  have hNL : ∀ {Y : Subgroup G}, Y ≤ normalizer (Y : Set G) →
      (∀ g ∈ Y, g ∈ normalizer ((pCoreOf 2 (conjJoin S L) : Subgroup G) : Set G)) →
      pCoreOf 2 (conjJoin S L) ⊓ Y ≤ pCoreOf 2 Y := by
    intro Y hYn hYN
    refine C1.le_pCoreOf_of_normalized inf_le_right (fun g hg => ?_)
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _).to_le inf_le_left)
    rw [← Lin2.conjR_eq_self_iff]
    show conjSubgroup (pCoreOf 2 (conjJoin S L) ⊓ Y) g = _
    rw [C5.conjSubgroup_inf, C5.conjSubgroup_eq_self (hYN g hg), C5.conjSubgroup_eq_self (hYn hg)]
  have key : ∀ (Y : Subgroup G) (c d : G), Y ≤ conjJoin S L →
      (∀ g ∈ Y, g ∈ normalizer ((pCoreOf 2 (conjJoin S L) : Subgroup G) : Set G)) →
      Y ≤ normalizer (Y : Set G) → c ∈ Y → (∀ y ∈ Y, d * y = y * d) → c * d = q →
      ∀ y ∈ Y, c * y * c⁻¹ * y⁻¹ ∈ pCoreOf 2 Y := by
    intro Y c d hYK hYN hYn hc hd hcd y hy
    have e : c * y * c⁻¹ * y⁻¹ = q * y * q⁻¹ * y⁻¹ := by
      rw [← hcd]
      have h1 := hd y hy
      calc c * y * c⁻¹ * y⁻¹ = c * (d * y * d⁻¹) * c⁻¹ * y⁻¹ := by
            rw [show d * y * d⁻¹ = y by rw [h1]; group]
        _ = (c * d) * y * (c * d)⁻¹ * y⁻¹ := by group
    have h1 : q * y * q⁻¹ * y⁻¹ ∈ pCoreOf 2 (conjJoin S L) := by
      have h2 : y * q⁻¹ * y⁻¹ ∈ pCoreOf 2 (conjJoin S L) :=
        (Subgroup.mem_normalizer_iff.1 (hNn y (hYK hy)) q⁻¹).1
          ((pCoreOf 2 (conjJoin S L)).inv_mem hq)
      have e2 : q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) := by group
      rw [e2]
      exact (pCoreOf 2 (conjJoin S L)).mul_mem hq h2
    have h3 : c * y * c⁻¹ * y⁻¹ ∈ Y :=
      Y.mul_mem (Y.mul_mem (Y.mul_mem hc hy) (Y.inv_mem hc)) (Y.inv_mem hy)
    exact hNL hYn hYN (Subgroup.mem_inf.2 ⟨by rw [e]; exact h1, h3⟩)
  have haQ : a ∈ blockQ L := by
    refine mem_blockQ_of_comm_alt5 hD.h5 ha ?_
    exact key L a b hLK (fun g hg => hNn g (hLK hg)) Subgroup.le_normalizer ha
      (fun y hy => (hD.comm_elem y hy b hb).symm) hab'
  have hbQ : b ∈ blockQ (conjR L t) := by
    refine mem_blockQ_of_comm_alt5 hD.h5₂ hb ?_
    refine key (conjR L t) b a hL₂K (fun g hg => hNn g (hL₂K hg)) Subgroup.le_normalizer hb
      (fun y hy => hD.comm_elem a ha y hy) ?_
    rw [← hab']
    exact (hD.comm_elem a ha b hb).symm
  rw [← hab']
  exact (blockQ L ⊔ blockQ (conjR L t)).mul_mem (Subgroup.mem_sup_left haQ)
    (Subgroup.mem_sup_right hbQ)

theorem blockQ_conjR_eq : blockQ (conjR L t) = blockU2 L t := by
  have h := C5.conjSubgroup_pCoreOf 2 L t
  have h2 : blockQ (conjR L t) = conjR (blockQ L) t := h.symm
  rw [h2, X.blockQ_eq_blockU]
  rfl

theorem blockU0_eq_pCoreOf : blockU0 S L = pCoreOf 2 (conjJoin S L) := by
  have hD := X.C.D
  rw [hD.blockU0_eq]
  apply le_antisymm
  · refine sup_le ((C1.blockU_le_blockQ hD.hL).trans (C56.blockQ_le_pCoreOf_conjJoin hD.hcs)) ?_
    have h1 : blockU2 L t ≤ blockQ (conjR L t) := by
      rw [X.blockQ_conjR_eq]
    have h2 := C56.blockQ_le_pCoreOf_conjJoin hD.swap_cs
    rw [hD.conjJoin_L₂] at h2
    exact h1.trans h2
  · refine X.pCoreOf_conjJoin_le_Q.trans (sup_le ?_ ?_)
    · rw [X.blockQ_eq_blockU]; exact le_sup_left
    · rw [X.blockQ_conjR_eq]; exact le_sup_right

end Two

end CFSG.QuasithinUnique.AppCS2
