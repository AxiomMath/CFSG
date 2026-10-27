module

public import CFSG.LieType.SeitzGeneration.RegimesOuterNarrow

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

@[expose] def IsG2Index (d : TauCeti.LieTypeIndex) : Prop := ∃ q : TauCeti.PrimePower, d = .G2 q

@[expose] def IsTrialityIndex (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d = .trialityD4 q

@[expose] def IsF4Index (d : TauCeti.LieTypeIndex) : Prop := ∃ q : TauCeti.PrimePower, d = .F4 q

@[expose] def IsE6Index (d : TauCeti.LieTypeIndex) : Prop := ∃ q : TauCeti.PrimePower, d = .E6 q

@[expose] def IsTwistedE6Index (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d = .twistedE6 q

@[expose] def IsE7Index (d : TauCeti.LieTypeIndex) : Prop := ∃ q : TauCeti.PrimePower, d = .E7 q

@[expose] def IsE8Index (d : TauCeti.LieTypeIndex) : Prop := ∃ q : TauCeti.PrimePower, d = .E8 q

@[expose] def IsSuzukiIndex (d : TauCeti.LieTypeIndex) : Prop := ∃ m : ℕ, d = .suzuki m

@[expose] def IsReeG2Index (d : TauCeti.LieTypeIndex) : Prop := ∃ m : ℕ, d = .reeG2 m

@[expose] def IsReeF4Index (d : TauCeti.LieTypeIndex) : Prop := ∃ m : ℕ, d = .reeF4 m

@[expose] def IsTitsIndex (d : TauCeti.LieTypeIndex) : Prop := d = .tits

@[expose] def IsUntwistedExcIndex (d : TauCeti.LieTypeIndex) : Prop :=
  IsG2Index d ∨ IsF4Index d ∨ IsE6Index d ∨ IsE7Index d ∨ IsE8Index d

@[expose] def IsTwistedExcIndex (d : TauCeti.LieTypeIndex) : Prop :=
  IsTrialityIndex d ∨ IsTwistedE6Index d

@[expose] def IsChevalleyExcIndex (d : TauCeti.LieTypeIndex) : Prop :=
  IsUntwistedExcIndex d ∨ IsTwistedExcIndex d

@[expose] def IsReeTypeIndex (d : TauCeti.LieTypeIndex) : Prop :=
  IsSuzukiIndex d ∨ IsReeG2Index d ∨ IsReeF4Index d ∨ IsTitsIndex d

theorem not_isClassicalIndex_iff (d : TauCeti.LieTypeIndex) :
    ¬ IsClassicalIndex d ↔ IsChevalleyExcIndex d ∨ IsReeTypeIndex d := by
  cases d <;> simp [IsClassicalIndex, IsChevalleyExcIndex, IsReeTypeIndex, IsUntwistedExcIndex,
    IsTwistedExcIndex, IsG2Index, IsTrialityIndex, IsF4Index, IsE6Index, IsTwistedE6Index,
    IsE7Index, IsE8Index, IsSuzukiIndex, IsReeG2Index, IsReeF4Index, IsTitsIndex]

theorem IsChevalleyExcIndex.not_classical {d : TauCeti.LieTypeIndex} (h : IsChevalleyExcIndex d) :
    ¬ IsClassicalIndex d :=
  (not_isClassicalIndex_iff d).mpr (Or.inl h)

theorem IsReeTypeIndex.not_classical {d : TauCeti.LieTypeIndex} (h : IsReeTypeIndex d) :
    ¬ IsClassicalIndex d :=
  (not_isClassicalIndex_iff d).mpr (Or.inr h)

theorem IsG2Index.not_classical {d : TauCeti.LieTypeIndex} (h : IsG2Index d) :
    ¬ IsClassicalIndex d :=
  IsChevalleyExcIndex.not_classical (Or.inl (Or.inl h))

theorem IsTrialityIndex.not_classical {d : TauCeti.LieTypeIndex} (h : IsTrialityIndex d) :
    ¬ IsClassicalIndex d :=
  IsChevalleyExcIndex.not_classical (Or.inr (Or.inl h))

theorem IsF4Index.not_classical {d : TauCeti.LieTypeIndex} (h : IsF4Index d) :
    ¬ IsClassicalIndex d :=
  IsChevalleyExcIndex.not_classical (Or.inl (Or.inr (Or.inl h)))

theorem IsE6Index.not_classical {d : TauCeti.LieTypeIndex} (h : IsE6Index d) :
    ¬ IsClassicalIndex d :=
  IsChevalleyExcIndex.not_classical (Or.inl (Or.inr (Or.inr (Or.inl h))))

theorem IsTwistedE6Index.not_classical {d : TauCeti.LieTypeIndex} (h : IsTwistedE6Index d) :
    ¬ IsClassicalIndex d :=
  IsChevalleyExcIndex.not_classical (Or.inr (Or.inr h))

theorem IsE7Index.not_classical {d : TauCeti.LieTypeIndex} (h : IsE7Index d) :
    ¬ IsClassicalIndex d :=
  IsChevalleyExcIndex.not_classical (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem IsE8Index.not_classical {d : TauCeti.LieTypeIndex} (h : IsE8Index d) :
    ¬ IsClassicalIndex d :=
  IsChevalleyExcIndex.not_classical (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem IsSuzukiIndex.not_classical {d : TauCeti.LieTypeIndex} (h : IsSuzukiIndex d) :
    ¬ IsClassicalIndex d :=
  IsReeTypeIndex.not_classical (Or.inl h)

theorem IsReeG2Index.not_classical {d : TauCeti.LieTypeIndex} (h : IsReeG2Index d) :
    ¬ IsClassicalIndex d :=
  IsReeTypeIndex.not_classical (Or.inr (Or.inl h))

theorem IsReeF4Index.not_classical {d : TauCeti.LieTypeIndex} (h : IsReeF4Index d) :
    ¬ IsClassicalIndex d :=
  IsReeTypeIndex.not_classical (Or.inr (Or.inr (Or.inl h)))

theorem IsTitsIndex.not_classical {d : TauCeti.LieTypeIndex} (h : IsTitsIndex d) :
    ¬ IsClassicalIndex d :=
  IsReeTypeIndex.not_classical (Or.inr (Or.inr (Or.inr h)))

@[expose] def SeitzExcParabolicFor (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  SeitzPlanes fun d p E => InnerPlane d p E ∧ P d.1 ∧ NormalizesRSubgroup d E

@[expose] def SeitzExcAnisotropicFor (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  SeitzPlanes fun d p E =>
    InnerPlane d p E ∧ P d.1 ∧ RankLE2 p (Cat d) ∧ ¬ NormalizesRSubgroup d E

@[expose] def SeitzExcOuterNarrowFor (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E ∧ P d.1

theorem seitzExcParabolic_eq :
    SeitzExcParabolic = SeitzExcParabolicFor fun d => ¬ IsClassicalIndex d := rfl

theorem seitzExcAnisotropic_eq :
    SeitzExcAnisotropic = SeitzExcAnisotropicFor fun d => ¬ IsClassicalIndex d := rfl

@[expose] def SeitzExcOuterNarrow : Prop :=
  SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E ∧ ¬ IsClassicalIndex d.1

theorem seitzExcOuterNarrow_eq :
    SeitzExcOuterNarrow = SeitzExcOuterNarrowFor fun d => ¬ IsClassicalIndex d := rfl

theorem SeitzExcParabolic.toFor (h : SeitzExcParabolic) :
    SeitzExcParabolicFor fun d => ¬ IsClassicalIndex d := h

theorem SeitzExcAnisotropic.toFor (h : SeitzExcAnisotropic) :
    SeitzExcAnisotropicFor fun d => ¬ IsClassicalIndex d := h

theorem SeitzExcOuterNarrow.toFor (h : SeitzExcOuterNarrow) :
    SeitzExcOuterNarrowFor fun d => ¬ IsClassicalIndex d := h

theorem SeitzExcParabolic.ofFor (h : SeitzExcParabolicFor fun d => ¬ IsClassicalIndex d) :
    SeitzExcParabolic := h

theorem SeitzExcAnisotropic.ofFor (h : SeitzExcAnisotropicFor fun d => ¬ IsClassicalIndex d) :
    SeitzExcAnisotropic := h

theorem SeitzExcOuterNarrow.ofFor (h : SeitzExcOuterNarrowFor fun d => ¬ IsClassicalIndex d) :
    SeitzExcOuterNarrow := h

theorem SeitzExcParabolicFor.mono {P Q : TauCeti.LieTypeIndex → Prop} (h : ∀ d, Q d → P d)
    (hP : SeitzExcParabolicFor P) : SeitzExcParabolicFor Q :=
  SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, h _ hE.2.1, hE.2.2⟩) hP

theorem SeitzExcAnisotropicFor.mono {P Q : TauCeti.LieTypeIndex → Prop} (h : ∀ d, Q d → P d)
    (hP : SeitzExcAnisotropicFor P) : SeitzExcAnisotropicFor Q :=
  SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, h _ hE.2.1, hE.2.2⟩) hP

theorem SeitzExcOuterNarrowFor.mono {P Q : TauCeti.LieTypeIndex → Prop} (h : ∀ d, Q d → P d)
    (hP : SeitzExcOuterNarrowFor P) : SeitzExcOuterNarrowFor Q :=
  SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, hE.2.1, h _ hE.2.2⟩) hP

theorem SeitzExcParabolicFor.union {P Q : TauCeti.LieTypeIndex → Prop}
    (hP : SeitzExcParabolicFor P) (hQ : SeitzExcParabolicFor Q) :
    SeitzExcParabolicFor fun d => P d ∨ Q d :=
  SeitzPlanes.of_cover (fun _ _ _ _ _ hE => by
    obtain ⟨hi, hPQ, hn⟩ := hE
    exact hPQ.imp (fun h => ⟨hi, h, hn⟩) (fun h => ⟨hi, h, hn⟩)) hP hQ

theorem SeitzExcAnisotropicFor.union {P Q : TauCeti.LieTypeIndex → Prop}
    (hP : SeitzExcAnisotropicFor P) (hQ : SeitzExcAnisotropicFor Q) :
    SeitzExcAnisotropicFor fun d => P d ∨ Q d :=
  SeitzPlanes.of_cover (fun _ _ _ _ _ hE => by
    obtain ⟨hi, hPQ, hr, hn⟩ := hE
    exact hPQ.imp (fun h => ⟨hi, h, hr, hn⟩) (fun h => ⟨hi, h, hr, hn⟩)) hP hQ

theorem SeitzExcOuterNarrowFor.union {P Q : TauCeti.LieTypeIndex → Prop}
    (hP : SeitzExcOuterNarrowFor P) (hQ : SeitzExcOuterNarrowFor Q) :
    SeitzExcOuterNarrowFor fun d => P d ∨ Q d :=
  SeitzPlanes.of_cover (fun _ _ _ _ _ hE => by
    obtain ⟨hi, hs, hPQ⟩ := hE
    exact hPQ.imp (fun h => ⟨hi, hs, h⟩) (fun h => ⟨hi, hs, h⟩)) hP hQ

@[expose] def SeitzExcParabolicUntw : Prop := SeitzExcParabolicFor IsUntwistedExcIndex

@[expose] def SeitzExcParabolicTw : Prop := SeitzExcParabolicFor IsTwistedExcIndex

@[expose] def SeitzExcParabolicChev : Prop := SeitzExcParabolicFor IsChevalleyExcIndex

@[expose] def SeitzExcParabolicRee : Prop := SeitzExcParabolicFor IsReeTypeIndex

theorem seitzExcParabolicChev_of_parts (hU : SeitzExcParabolicUntw) (hT : SeitzExcParabolicTw) :
    SeitzExcParabolicChev :=
  SeitzExcParabolicFor.union hU hT

theorem seitzExcParabolicRee_of_parts (hS : SeitzExcParabolicFor IsSuzukiIndex)
    (hG : SeitzExcParabolicFor IsReeG2Index) (hF : SeitzExcParabolicFor IsReeF4Index)
    (hT : SeitzExcParabolicFor IsTitsIndex) : SeitzExcParabolicRee :=
  SeitzExcParabolicFor.union hS (SeitzExcParabolicFor.union hG (SeitzExcParabolicFor.union hF hT))

theorem seitzExcParabolic_of_parts (hC : SeitzExcParabolicChev) (hR : SeitzExcParabolicRee) :
    SeitzExcParabolic :=
  SeitzExcParabolic.ofFor
    ((SeitzExcParabolicFor.union hC hR).mono fun d hd => (not_isClassicalIndex_iff d).mp hd)

theorem seitzExcParabolic_iff :
    SeitzExcParabolic ↔ SeitzExcParabolicChev ∧ SeitzExcParabolicRee :=
  ⟨fun h => ⟨h.toFor.mono fun _ hd => hd.not_classical, h.toFor.mono fun _ hd => hd.not_classical⟩,
    fun h => seitzExcParabolic_of_parts h.1 h.2⟩

@[expose] def SeitzExcAnisotropicG2 : Prop := SeitzExcAnisotropicFor IsG2Index

@[expose] def SeitzExcAnisotropicTriality : Prop := SeitzExcAnisotropicFor IsTrialityIndex

@[expose] def SeitzExcAnisotropicF4 : Prop := SeitzExcAnisotropicFor IsF4Index

@[expose] def SeitzExcAnisotropicE6 : Prop := SeitzExcAnisotropicFor IsE6Index

@[expose] def SeitzExcAnisotropicTwistedE6 : Prop := SeitzExcAnisotropicFor IsTwistedE6Index

@[expose] def SeitzExcAnisotropicE7 : Prop := SeitzExcAnisotropicFor IsE7Index

@[expose] def SeitzExcAnisotropicE8 : Prop := SeitzExcAnisotropicFor IsE8Index

@[expose] def SeitzExcAnisotropicSuzuki : Prop := SeitzExcAnisotropicFor IsSuzukiIndex

@[expose] def SeitzExcAnisotropicReeG2 : Prop := SeitzExcAnisotropicFor IsReeG2Index

@[expose] def SeitzExcAnisotropicReeF4 : Prop := SeitzExcAnisotropicFor IsReeF4Index

@[expose] def SeitzExcAnisotropicTits : Prop := SeitzExcAnisotropicFor IsTitsIndex

structure SeitzExcAnisotropicFamilies : Prop where
  g2 : SeitzExcAnisotropicG2
  triality : SeitzExcAnisotropicTriality
  f4 : SeitzExcAnisotropicF4
  e6 : SeitzExcAnisotropicE6
  twistedE6 : SeitzExcAnisotropicTwistedE6
  e7 : SeitzExcAnisotropicE7
  e8 : SeitzExcAnisotropicE8
  suzuki : SeitzExcAnisotropicSuzuki
  reeG2 : SeitzExcAnisotropicReeG2
  reeF4 : SeitzExcAnisotropicReeF4
  tits : SeitzExcAnisotropicTits

theorem SeitzExcAnisotropicFamilies.toAnisotropic (h : SeitzExcAnisotropicFamilies) :
    SeitzExcAnisotropic := by
  intro d p hp hp2 hpd hex E hE hc ⟨hi, hnc, hr, hn⟩
  rcases (not_isClassicalIndex_iff d.1).mp hnc with
    ((hd | hd | hd | hd | hd) | (hd | hd)) | (hd | hd | hd | hd)
  · exact h.g2 d p hp hp2 hpd hex E hE hc ⟨hi, hd, hr, hn⟩
  · exact h.f4 d p hp hp2 hpd hex E hE hc ⟨hi, hd, hr, hn⟩
  · exact h.e6 d p hp hp2 hpd hex E hE hc ⟨hi, hd, hr, hn⟩
  · exact h.e7 d p hp hp2 hpd hex E hE hc ⟨hi, hd, hr, hn⟩
  · exact h.e8 d p hp hp2 hpd hex E hE hc ⟨hi, hd, hr, hn⟩
  · exact h.triality d p hp hp2 hpd hex E hE hc ⟨hi, hd, hr, hn⟩
  · exact h.twistedE6 d p hp hp2 hpd hex E hE hc ⟨hi, hd, hr, hn⟩
  · exact h.suzuki d p hp hp2 hpd hex E hE hc ⟨hi, hd, hr, hn⟩
  · exact h.reeG2 d p hp hp2 hpd hex E hE hc ⟨hi, hd, hr, hn⟩
  · exact h.reeF4 d p hp hp2 hpd hex E hE hc ⟨hi, hd, hr, hn⟩
  · exact h.tits d p hp hp2 hpd hex E hE hc ⟨hi, hd, hr, hn⟩

theorem SeitzExcAnisotropic.families (h : SeitzExcAnisotropic) : SeitzExcAnisotropicFamilies where
  g2 := SeitzExcAnisotropicFor.mono (fun _ hd => hd.not_classical) h.toFor
  triality := SeitzExcAnisotropicFor.mono (fun _ hd => hd.not_classical) h.toFor
  f4 := SeitzExcAnisotropicFor.mono (fun _ hd => hd.not_classical) h.toFor
  e6 := SeitzExcAnisotropicFor.mono (fun _ hd => hd.not_classical) h.toFor
  twistedE6 := SeitzExcAnisotropicFor.mono (fun _ hd => hd.not_classical) h.toFor
  e7 := SeitzExcAnisotropicFor.mono (fun _ hd => hd.not_classical) h.toFor
  e8 := SeitzExcAnisotropicFor.mono (fun _ hd => hd.not_classical) h.toFor
  suzuki := SeitzExcAnisotropicFor.mono (fun _ hd => hd.not_classical) h.toFor
  reeG2 := SeitzExcAnisotropicFor.mono (fun _ hd => hd.not_classical) h.toFor
  reeF4 := SeitzExcAnisotropicFor.mono (fun _ hd => hd.not_classical) h.toFor
  tits := SeitzExcAnisotropicFor.mono (fun _ hd => hd.not_classical) h.toFor

theorem seitzExcAnisotropic_iff : SeitzExcAnisotropic ↔ SeitzExcAnisotropicFamilies :=
  ⟨SeitzExcAnisotropic.families, SeitzExcAnisotropicFamilies.toAnisotropic⟩

@[expose] def SeitzExcOuterNarrowG2 : Prop := SeitzExcOuterNarrowFor IsG2Index

@[expose] def SeitzExcOuterNarrowTriality : Prop := SeitzExcOuterNarrowFor IsTrialityIndex

@[expose] def SeitzExcOuterNarrowF4 : Prop := SeitzExcOuterNarrowFor IsF4Index

@[expose] def SeitzExcOuterNarrowE6 : Prop := SeitzExcOuterNarrowFor IsE6Index

@[expose] def SeitzExcOuterNarrowTwistedE6 : Prop := SeitzExcOuterNarrowFor IsTwistedE6Index

@[expose] def SeitzExcOuterNarrowE7 : Prop := SeitzExcOuterNarrowFor IsE7Index

@[expose] def SeitzExcOuterNarrowE8 : Prop := SeitzExcOuterNarrowFor IsE8Index

@[expose] def SeitzExcOuterNarrowSuzuki : Prop := SeitzExcOuterNarrowFor IsSuzukiIndex

@[expose] def SeitzExcOuterNarrowReeG2 : Prop := SeitzExcOuterNarrowFor IsReeG2Index

@[expose] def SeitzExcOuterNarrowReeF4 : Prop := SeitzExcOuterNarrowFor IsReeF4Index

@[expose] def SeitzExcOuterNarrowTits : Prop := SeitzExcOuterNarrowFor IsTitsIndex

structure SeitzExcOuterNarrowFamilies : Prop where
  g2 : SeitzExcOuterNarrowG2
  triality : SeitzExcOuterNarrowTriality
  f4 : SeitzExcOuterNarrowF4
  e6 : SeitzExcOuterNarrowE6
  twistedE6 : SeitzExcOuterNarrowTwistedE6
  e7 : SeitzExcOuterNarrowE7
  e8 : SeitzExcOuterNarrowE8
  suzuki : SeitzExcOuterNarrowSuzuki
  reeG2 : SeitzExcOuterNarrowReeG2
  reeF4 : SeitzExcOuterNarrowReeF4
  tits : SeitzExcOuterNarrowTits

theorem SeitzExcOuterNarrowFamilies.toOuterNarrow (h : SeitzExcOuterNarrowFamilies) :
    SeitzExcOuterNarrow := by
  intro d p hp hp2 hpd hex E hE hc ⟨hi, hs, hnc⟩
  rcases (not_isClassicalIndex_iff d.1).mp hnc with
    ((hd | hd | hd | hd | hd) | (hd | hd)) | (hd | hd | hd | hd)
  · exact h.g2 d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩
  · exact h.f4 d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩
  · exact h.e6 d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩
  · exact h.e7 d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩
  · exact h.e8 d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩
  · exact h.triality d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩
  · exact h.twistedE6 d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩
  · exact h.suzuki d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩
  · exact h.reeG2 d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩
  · exact h.reeF4 d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩
  · exact h.tits d p hp hp2 hpd hex E hE hc ⟨hi, hs, hd⟩

theorem SeitzExcOuterNarrow.families (h : SeitzExcOuterNarrow) : SeitzExcOuterNarrowFamilies where
  g2 := SeitzExcOuterNarrowFor.mono (fun _ hd => hd.not_classical) h.toFor
  triality := SeitzExcOuterNarrowFor.mono (fun _ hd => hd.not_classical) h.toFor
  f4 := SeitzExcOuterNarrowFor.mono (fun _ hd => hd.not_classical) h.toFor
  e6 := SeitzExcOuterNarrowFor.mono (fun _ hd => hd.not_classical) h.toFor
  twistedE6 := SeitzExcOuterNarrowFor.mono (fun _ hd => hd.not_classical) h.toFor
  e7 := SeitzExcOuterNarrowFor.mono (fun _ hd => hd.not_classical) h.toFor
  e8 := SeitzExcOuterNarrowFor.mono (fun _ hd => hd.not_classical) h.toFor
  suzuki := SeitzExcOuterNarrowFor.mono (fun _ hd => hd.not_classical) h.toFor
  reeG2 := SeitzExcOuterNarrowFor.mono (fun _ hd => hd.not_classical) h.toFor
  reeF4 := SeitzExcOuterNarrowFor.mono (fun _ hd => hd.not_classical) h.toFor
  tits := SeitzExcOuterNarrowFor.mono (fun _ hd => hd.not_classical) h.toFor

theorem seitzExcOuterNarrow_iff : SeitzExcOuterNarrow ↔ SeitzExcOuterNarrowFamilies :=
  ⟨SeitzExcOuterNarrow.families, SeitzExcOuterNarrowFamilies.toOuterNarrow⟩

end CFSG.LieType.SeitzGeneration
