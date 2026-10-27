module

public import CFSG.Sporadic.Co1Block.Cent
public import CFSG.Sporadic.Co1Block.Co1Equiv
public import Certificates.Certificate129070
public import CFSG.Sporadic.Co1.Module.InvSpec

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier

theorem forall₂_comm_of_all {R : List Native.Rows} {gs : List GL24}
    (h : List.Forall₂ MRep R gs) {tR : Native.Rows} {t : GL24} (ht : MRep tR t)
    (hc : R.all (fun g => Native.mul g tR == Native.mul tR g) = true) :
    ∀ g ∈ gs, g * t = t * g := by
  intro g hg
  obtain ⟨r, hr, hrg⟩ := forall₂_mem_left h hg
  have e : Native.mul r tR = Native.mul tR r := by
    have := List.all_eq_true.1 hc r hr
    simpa using this
  exact (hrg.mul ht).eq (e ▸ ht.mul hrg)

theorem f0_facts :
    ∃ b s₁ s₂ : GL24, b ∈ GA ∧ s₁ ∈ GA ∧ s₂ ∈ GA ∧ b * b = 1 ∧ b ≠ 1 ∧ b ≠ (iotaA : GL24) ∧
      (iotaA : GL24) * b = b * (iotaA : GL24) ∧
      s₁ * (iotaA : GL24) * s₁⁻¹ = b ∧ s₁ * b * s₁⁻¹ = (iotaA : GL24) ∧
      s₂ * b * s₂⁻¹ = (iotaA : GL24) * b ∧ s₂ * ((iotaA : GL24) * b) * s₂⁻¹ = b ∧
      (GA ⊓ Subgroup.centralizer {(iotaA : GL24)}) ⊔ (GA ⊓ Subgroup.centralizer {b}) = GA := by
  have hc := Certificates.certificate129070
  unfold f0Check at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hD1, hD2⟩, hidx⟩, hIB⟩, hS1⟩, hS2⟩, hcA⟩, hcB⟩, hab⟩, hbb⟩, hvb⟩,
    hva⟩, hb1⟩, hba⟩, hs1a⟩, hs1b⟩, hs2b⟩, hs2ab⟩, hA1⟩, hA2⟩ := hc
  set t : GL24 := (iotaA : GL24) with ht
  have htG : t ∈ GA := iotaA_mem_GA
  have ha : MRep iotaARows t := rep_iotaA
  have hdag := rep_brayDag (d₁ := f0D1) ha hD1
  have hdagG := brayDag_mem_GA (d₁ := f0D1) htG
  set bG : GL24 := (brayDagG t f0D1).getD (f0IB - 1) 1 with hbG
  set s₁G : GL24 := (brayDagG t f0D1).getD (f0S1 - 1) 1 with hs₁G
  set s₂G : GL24 := (brayDagG t f0D1).getD (f0S2 - 1) 1 with hs₂G
  have hb : MRep ((Native.brayRows iotaARows f0D1).1.getD (f0IB - 1) Native.one) bG :=
    getD_rep hdag MRep.one _
  have hs₁ : MRep ((Native.brayRows iotaARows f0D1).1.getD (f0S1 - 1) Native.one) s₁G :=
    getD_rep hdag MRep.one _
  have hs₂ : MRep ((Native.brayRows iotaARows f0D1).1.getD (f0S2 - 1) Native.one) s₂G :=
    getD_rep hdag MRep.one _
  have hbGA : bG ∈ GA := getD_mem_of_forall hdagG _
  have hs₁GA : s₁G ∈ GA := getD_mem_of_forall hdagG _
  have hs₂GA : s₂G ∈ GA := getD_mem_of_forall hdagG _
  obtain ⟨rb, hrb⟩ : ∃ rb, (Native.brayRows iotaARows f0D1).1.getD (f0IB - 1) Native.one = rb :=
    ⟨_, rfl⟩
  obtain ⟨r₁, hr₁⟩ : ∃ r, (Native.brayRows iotaARows f0D1).1.getD (f0S1 - 1) Native.one = r :=
    ⟨_, rfl⟩
  obtain ⟨r₂, hr₂⟩ : ∃ r, (Native.brayRows iotaARows f0D1).1.getD (f0S2 - 1) Native.one = r :=
    ⟨_, rfl⟩
  rw [hrb] at hb hab hbb hvb hb1 hba hs1a hs1b hs2b hs2ab hcB
  rw [hr₁] at hs₁ hs1a hs1b
  rw [hr₂] at hs₂ hs2b hs2ab
  have hab' : t * bG = bG * t := (ha.mul hb).eq (hab ▸ hb.mul ha)
  have hbb' : bG * bG = 1 := (hb.mul hb).eq (hbb ▸ MRep.one)
  have hb1' : bG ≠ 1 := by
    intro h
    apply hb1
    rw [h] at hb
    exact CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid hvb validRows_one
      (hb.trans MRep.one.symm)
  have hba' : bG ≠ t := by
    intro h
    apply hba
    rw [h] at hb
    exact CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid hvb hva (hb.trans ha.symm)
  have hs1a' : s₁G * t = bG * s₁G := (hs₁.mul ha).eq (hs1a ▸ hb.mul hs₁)
  have hs1b' : s₁G * bG = t * s₁G := (hs₁.mul hb).eq (hs1b ▸ ha.mul hs₁)
  have hs2b' : s₂G * bG = (t * bG) * s₂G := (hs₂.mul hb).eq (hs2b ▸ (ha.mul hb).mul hs₂)
  have hs2ab' : s₂G * (t * bG) = bG * s₂G := (hs₂.mul (ha.mul hb)).eq (hs2ab ▸ hb.mul hs₂)
  refine ⟨bG, s₁G, s₂G, hbGA, hs₁GA, hs₂GA, hbb', hb1', hba', hab', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs1a']; group
  · rw [hs1b']; group
  · rw [hs2b']; group
  · rw [hs2ab']; group
  ·
    have hrepE := rep_brayElts (bidx := f0Bidx) ha hD1
    have hrepD2 := dag_rep hrepE f0D2 hD2
    set H := brayE t f0D1 f0Bidx with hH
    have hA₁ : A₁ ∈ H := by
      have hr := getD_rep hrepD2 MRep.one
        ((Native.dag (Native.brayElts (Native.brayRows iotaARows f0D1) f0Bidx) f0D2).1.length - 2)
      rw [hA1] at hr
      have : (dagG (brayEltsG t f0D1 f0Bidx) f0D2).getD
          ((Native.dag (Native.brayElts (Native.brayRows iotaARows f0D1) f0Bidx) f0D2).1.length - 2)
          1 = A₁ := (hr.eq rep_A₁)
      rw [← this]
      exact getD_mem_of_forall (H := H) (gs := dagG (brayEltsG t f0D1 f0Bidx) f0D2)
        (fun g hg => strongDag_mem g hg) _
    have hA₂ : A₂ ∈ H := by
      have hr := getD_rep hrepD2 MRep.one
        ((Native.dag (Native.brayElts (Native.brayRows iotaARows f0D1) f0Bidx) f0D2).1.length - 1)
      rw [hA2] at hr
      have : (dagG (brayEltsG t f0D1 f0Bidx) f0D2).getD
          ((Native.dag (Native.brayElts (Native.brayRows iotaARows f0D1) f0Bidx) f0D2).1.length - 1)
          1 = A₂ := (hr.eq rep_A₂)
      rw [← this]
      exact getD_mem_of_forall (H := H) (gs := dagG (brayEltsG t f0D1 f0Bidx) f0D2)
        (fun g hg => strongDag_mem g hg) _
    have hGAH : GA ≤ H := by
      rw [GA_eq]
      refine (Subgroup.closure_le H).2 ?_
      intro x hx
      rcases hx with h | h
      · rw [h]; exact hA₁
      · rw [Set.mem_singleton_iff.1 h]; exact hA₂
    have hsplit : brayEltsG t f0D1 f0Bidx =
        brayEltsG t f0D1 (f0Bidx.take 8) ++ brayEltsG t f0D1 (f0Bidx.drop 8) := by
      unfold brayEltsG
      rw [← List.map_append, List.take_append_drop]
    have hc₁ := forall₂_comm_of_all (rep_brayElts (bidx := f0Bidx.take 8) ha hD1) ha hcA
    have hc₂ := forall₂_comm_of_all (rep_brayElts (bidx := f0Bidx.drop 8) ha hD1) hb hcB
    have hm₁ := brayElts_mem_GA (d₁ := f0D1) (bidx := f0Bidx.take 8) htG
    have hm₂ := brayElts_mem_GA (d₁ := f0D1) (bidx := f0Bidx.drop 8) htG
    have hHle : H ≤ (GA ⊓ Subgroup.centralizer {t}) ⊔ (GA ⊓ Subgroup.centralizer {bG}) := by
      refine (Subgroup.closure_le _).2 fun g hg => ?_
      have hg' : g ∈ brayEltsG t f0D1 f0Bidx := hg
      rw [hsplit, List.mem_append] at hg'
      rcases hg' with h | h
      · exact Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hm₁ g h,
          Subgroup.mem_centralizer_singleton_iff.2 (hc₁ g h)⟩)
      · exact Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hm₂ g h,
          Subgroup.mem_centralizer_singleton_iff.2 (hc₂ g h)⟩)
    exact le_antisymm (sup_le inf_le_left inf_le_left) (hGAH.trans hHle)


end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
