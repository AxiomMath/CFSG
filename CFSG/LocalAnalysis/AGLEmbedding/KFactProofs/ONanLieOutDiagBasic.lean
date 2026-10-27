module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutBasic

public section

namespace CFSG.AGLEmbedding.LieOut

open scoped commutatorElement

theorem nat_card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 5)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 5), Fintype.card_fin] at h
  have h5 : Nat.factorial 5 = 120 := by decide
  omega

theorem nat_card_alt_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 7)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 7), Fintype.card_fin] at h
  have h7 : Nat.factorial 7 = 5040 := by decide
  omega

@[expose] def NoAp (p : ℕ) (S : Type) [Group S] : Prop :=
  ∀ (R : Type) [Group R] [Finite R] (ι : R →* alternatingGroup (Fin p)),
    Function.Injective ι → ∀ f : R →* S, Function.Surjective f → False

theorem NoAp.of_card_lt {p : ℕ} {S : Type} [Group S] [Finite S]
    (h : Nat.card (alternatingGroup (Fin p)) < Nat.card S) : NoAp p S := by
  intro R _ _ ι hι f hf
  have h1 : Nat.card S ≤ Nat.card R := Nat.card_le_card_of_surjective f hf
  have h2 : Nat.card R ≤ Nat.card (alternatingGroup (Fin p)) := Nat.card_le_card_of_injective ι hι
  omega

theorem NoAp.of_mulEquiv {p : ℕ} {S S' : Type} [Group S] [Group S'] (e : S ≃* S') (h : NoAp p S) :
    NoAp p S' := by
  intro R _ _ ι hι f hf
  exact h R ι hι (e.symm.toMonoidHom.comp f) (e.symm.surjective.comp hf)

theorem noAp_seven_of_card_eq {S : Type} [Group S] [Finite S] (hS : Nat.card S = 504) :
    NoAp 7 S := by
  intro R _ _ ι hι f hf
  have hAsimple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hA : Nat.card (alternatingGroup (Fin 7)) = 2520 := nat_card_alt_seven
  have hSR : Nat.card S ∣ Nat.card R := by
    have := Subgroup.card_ker_mul_card_range f
    rw [MonoidHom.range_eq_top_of_surjective f hf, Subgroup.card_top] at this
    exact ⟨Nat.card f.ker, by rw [← this, mul_comm]⟩
  have hRA : Nat.card R ∣ 2520 := by
    rw [← hA]
    have := Subgroup.card_dvd_of_le (le_top : ι.range ≤ ⊤)
    rw [Nat.card_congr (MonoidHom.ofInjective hι).toEquiv.symm, Subgroup.card_top] at this
    exact this
  obtain ⟨m, hm⟩ := hSR
  rw [hS] at hm
  have hm5 : m ∣ 5 := by
    have h2 : 504 * m ∣ 504 * 5 := by rw [← hm]; norm_num [hRA]
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hm5 with h1 | h5
  ·
    set H : Subgroup (alternatingGroup (Fin 7)) := ι.range with hH
    have hHcard : Nat.card H = 504 := by
      rw [hH, ← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv, hm, h1]
    have hidx : H.index = 5 := by
      have := H.card_mul_index
      rw [hHcard, hA] at this
      omega
    have hker : (MulAction.toPermHom (alternatingGroup (Fin 7))
        (alternatingGroup (Fin 7) ⧸ H)).ker.Normal := inferInstance
    rcases (haveI := hker; hAsimple.eq_bot_or_eq_top_of_normal
      (MulAction.toPermHom (alternatingGroup (Fin 7)) (alternatingGroup (Fin 7) ⧸ H)).ker)
      with hbot | htop
    · have hinj := (MonoidHom.ker_eq_bot_iff _).1 hbot
      have h2 := Nat.card_le_card_of_injective _ hinj
      rw [hA, Nat.card_perm] at h2
      have hq : Nat.card (alternatingGroup (Fin 7) ⧸ H) = 5 := hidx
      rw [hq] at h2
      norm_num [Nat.factorial] at h2
    · have hHtop : H = ⊤ := by
        rw [eq_top_iff]
        intro a _
        have ha : a ∈ (MulAction.toPermHom (alternatingGroup (Fin 7))
            (alternatingGroup (Fin 7) ⧸ H)).ker := htop ▸ Subgroup.mem_top a
        have h1' := congrArg
          (fun σ => σ (((1 : alternatingGroup (Fin 7)) : alternatingGroup (Fin 7) ⧸ H)))
          (MonoidHom.mem_ker.1 ha)
        have h2' : (a : alternatingGroup (Fin 7) ⧸ H) =
            ((1 : alternatingGroup (Fin 7)) : alternatingGroup (Fin 7) ⧸ H) := by
          simpa [MulAction.toPermHom_apply, MulAction.Quotient.smul_mk] using h1'
        exact (QuotientGroup.eq.1 h2'.symm |> fun h => by simpa using H.inv_mem h)
      rw [hHtop, Subgroup.card_top, hA] at hHcard
      omega
  ·
    have hbij : Function.Bijective ι := by
      refine (Nat.bijective_iff_injective_and_card ι).2 ⟨hι, ?_⟩
      rw [hm, h5, hA]
    let e : R ≃* alternatingGroup (Fin 7) := MulEquiv.ofBijective ι hbij
    have hker : (f.comp e.symm.toMonoidHom).ker.Normal := inferInstance
    have hcard := Subgroup.card_ker_mul_card_range (f.comp e.symm.toMonoidHom)
    have hsurj : Function.Surjective (f.comp e.symm.toMonoidHom) := hf.comp e.symm.surjective
    rw [MonoidHom.range_eq_top_of_surjective _ hsurj, Subgroup.card_top, hA, hS] at hcard
    rcases (haveI := hker; hAsimple.eq_bot_or_eq_top_of_normal
      (f.comp e.symm.toMonoidHom).ker) with hbot | htop
    · rw [hbot, Subgroup.card_bot] at hcard
      omega
    · rw [htop, Subgroup.card_top, hA] at hcard
      omega

theorem isQuasisimple_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : CFSG.Open.IsQuasisimple G) : CFSG.Open.IsQuasisimple H :=
  h.of_mulEquiv e.symm

theorem center_eq_bot_of_isSimpleGroup_perfect {G : Type*} [Group G] [IsSimpleGroup G]
    (hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤) : Subgroup.center G = ⊥ := by
  rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G)) with h | h
  · exact h
  · exfalso
    have hc : ∀ a b : G, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm
    have hcomm : (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆) = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hc a b
    rw [hperf] at hcomm
    exact (IsSimpleGroup.toNontrivial (G := G)).exists_pair_ne.elim fun a ⟨b, hab⟩ => hab (by
      have : a ∈ (⊥ : Subgroup G) := hcomm ▸ Subgroup.mem_top a
      have h2 : b ∈ (⊥ : Subgroup G) := hcomm ▸ Subgroup.mem_top b
      rw [Subgroup.mem_bot] at this h2
      rw [this, h2])

theorem exists_quasisimple_of_node {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (hZ : ∀ z : ↥L, z ∈ Subgroup.center ↥L → (z : Y) ∈ J) {p : ℕ}
    {S : Subgroup (↥L ⧸ Subgroup.center ↥L)} (hSJ : S ≤ quotImage L J)
    (hS : ⁅S, S⁆ = S) (hSs : IsSimpleGroup ↥S) (hpS : p ∣ Nat.card S) (hno : NoAp p ↥S) :
    ∃ X : Subgroup Y, X ≤ J ∧ CFSG.Open.IsQuasisimple ↥X ∧ p ∣ Nat.card X ∧
      ∀ φ : ↥X →* alternatingGroup (Fin p), ¬ φ.ker ≤ Subgroup.center ↥X := by
  classical
  set π : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hπ
  have hker : π.ker ≤ Subgroup.center ↥L := by rw [hπ, QuotientGroup.ker_mk']
  have hrange : S ≤ π.range := by
    rw [MonoidHom.range_eq_top_of_surjective π (QuotientGroup.mk'_surjective _)]
    exact le_top
  obtain ⟨W, hW, hWle, hWmap⟩ := ParabPrime.exists_perfect_map_eq π hker hS hrange
  have hWJ : ∀ w ∈ W, (w : Y) ∈ J := by
    intro w hw
    have h1 : π w ∈ S := hWle hw
    obtain ⟨l, hlJ, hl⟩ := mem_quotImage.1 (hSJ h1)
    have hz : l⁻¹ * w ∈ Subgroup.center ↥L := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπ, QuotientGroup.mk'_apply, hl]
      simp [hπ])
    have e1 : (w : Y) = (l : Y) * ((l⁻¹ * w : ↥L) : Y) := by simp
    rw [e1]
    exact J.mul_mem hlJ (hZ _ hz)
  let f : ↥W →* ↥S := (π.comp W.subtype).codRestrict S (fun w => hWle w.2)
  have hf : Function.Surjective f := by
    intro s
    have hs : (s : ↥L ⧸ Subgroup.center ↥L) ∈ W.map π := hWmap ▸ s.2
    obtain ⟨w, hw, hws⟩ := hs
    exact ⟨⟨w, hw⟩, Subtype.ext hws⟩
  have hker_f : f.ker ≤ Subgroup.center ↥W := by
    intro w hw
    have hw1 : π (w : ↥L) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hw)
    have hc : (w : ↥L) ∈ Subgroup.center ↥L := hker (MonoidHom.mem_ker.2 hw1)
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro v
    exact Subtype.ext (hc v)
  have hScenter : Subgroup.center ↥S = ⊥ := by
    have := hSs
    refine center_eq_bot_of_isSimpleGroup_perfect ?_
    have h1 : (commutator ↥S).map S.subtype = ⁅S, S⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    rw [hS] at h1
    have h2 : (⊤ : Subgroup ↥S).map S.subtype = S := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    exact Subgroup.map_injective S.subtype_injective (h1.trans h2.symm)
  have hcenter_f : Subgroup.center ↥W ≤ f.ker := by
    intro z hz
    have : f z ∈ Subgroup.center ↥S := Subgroup.map_center_le_center hf ⟨z, hz, rfl⟩
    rw [hScenter, Subgroup.mem_bot] at this
    exact this
  have hcenter : Subgroup.center ↥W = f.ker := le_antisymm hcenter_f hker_f
  have hWq : CFSG.Open.IsQuasisimple ↥W := by
    refine ⟨?_, ?_⟩
    · have h1 : (commutator ↥W).map W.subtype = ⁅W, W⁆ := by
        rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
          Subgroup.range_subtype]
      rw [hW] at h1
      have h2 : (⊤ : Subgroup ↥W).map W.subtype = W := by
        rw [Subgroup.map_top, Subgroup.range_subtype]
      exact Subgroup.map_injective W.subtype_injective (h1.trans h2.symm)
    · have e : ↥W ⧸ f.ker ≃* ↥S := QuotientGroup.quotientKerEquivOfSurjective f hf
      have e' : ↥W ⧸ Subgroup.center ↥W ≃* ↥S :=
        (QuotientGroup.quotientMulEquivOfEq hcenter).trans e
      have := hSs
      exact e'.isSimpleGroup
  set X : Subgroup Y := W.map L.subtype with hX
  let eX : ↥W ≃* ↥X := Subgroup.equivMapOfInjective W L.subtype L.subtype_injective
  refine ⟨X, ?_, isQuasisimple_of_mulEquiv eX hWq, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hWJ w hw
  · have h1 : Nat.card X = Nat.card W := (Nat.card_congr eX.toEquiv).symm
    rw [h1]
    refine hpS.trans ?_
    have := Subgroup.card_ker_mul_card_range f
    rw [MonoidHom.range_eq_top_of_surjective f hf, Subgroup.card_top] at this
    exact ⟨Nat.card f.ker, by rw [← this, mul_comm]⟩
  · intro φ hφ
    set φ' : ↥W →* alternatingGroup (Fin p) := φ.comp eX.toMonoidHom with hφ'
    have hker' : φ'.ker ≤ f.ker := by
      intro w hw
      have h1 : eX w ∈ φ.ker := hw
      have h2 := hφ h1
      rw [← hcenter, Subgroup.mem_center_iff]
      intro v
      have := Subgroup.mem_center_iff.1 h2 (eX v)
      exact eX.injective (by simpa using this)
    let g : ↥W ⧸ φ'.ker →* ↥S := QuotientGroup.lift φ'.ker f hker'
    let r : ↥φ'.range ≃* ↥W ⧸ φ'.ker := (QuotientGroup.quotientKerEquivRange φ').symm
    have hg : Function.Surjective (g.comp r.toMonoidHom) := by
      intro s
      obtain ⟨w, rfl⟩ := hf s
      refine ⟨r.symm (QuotientGroup.mk w), ?_⟩
      simp [g]
    exact hno ↥φ'.range φ'.range.subtype (Subtype.val_injective) (g.comp r.toMonoidHom) hg


theorem quotCenter_mulEquiv {P S : Type*} [Group P] [Group S] (f : P →* S)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center P)
    (hperf : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = ⊤) :
    Nonempty (P ⧸ Subgroup.center P ≃* S ⧸ Subgroup.center S) := by
  set q : P →* S ⧸ Subgroup.center S := (QuotientGroup.mk' (Subgroup.center S)).comp f with hq
  have hqs : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hf
  have hker_q : q.ker = Subgroup.center P := by
    refine le_antisymm (fun n hn => ?_) (fun z hz => ?_)
    · have hn1 : f n ∈ Subgroup.center S := by
        have := MonoidHom.mem_ker.1 hn
        simpa [hq] using this
      have hcomm : ∀ v : P, ⁅n, v⁆ ∈ Subgroup.center P := fun v => hker (by
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.1 hn1 (f v)).symm)
      let h : P →* Subgroup.center P :=
        { toFun := fun v => ⟨⁅n, v⁆, hcomm v⟩
          map_one' := by apply Subtype.ext; simp
          map_mul' := fun v v' => by
            apply Subtype.ext
            have hc : v * ⁅n, v'⁆ * v⁻¹ = ⁅n, v'⁆ := by
              rw [Subgroup.mem_center_iff.1 (hcomm v') v, mul_inv_cancel_right]
            change ⁅n, v * v'⁆ = ⁅n, v⁆ * ⁅n, v'⁆
            calc ⁅n, v * v'⁆ = ⁅n, v⁆ * (v * ⁅n, v'⁆ * v⁻¹) := by
                  simp only [commutatorElement_def]; group
              _ = ⁅n, v⁆ * ⁅n, v'⁆ := by rw [hc] }
      have hle : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ ≤ h.ker := by
        rw [Subgroup.commutator_le]
        intro a _ b _
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact Subtype.ext (Subgroup.mem_center_iff.1 (h b).2 (h a))
      rw [hperf] at hle
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 (hle (Subgroup.mem_top g)))
      change ⁅n, g⁆ = 1 at this
      exact ((commutatorElement_eq_one_iff_mul_comm).1 this).symm
    · have : f z ∈ Subgroup.center S := Subgroup.map_center_le_center hf ⟨z, hz, rfl⟩
      exact (QuotientGroup.eq_one_iff _).2 this
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker_q.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hqs)⟩


theorem exists_quasisimple_of_cover {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (hZ : ∀ z : ↥L, z ∈ Subgroup.center ↥L → (z : Y) ∈ J) {p : ℕ}
    {G : Type} [Group G] [Finite G] (ρ : G →* (↥L ⧸ Subgroup.center ↥L))
    (hρJ : ρ.range ≤ quotImage L J) (hker : ρ.ker ≤ Subgroup.center G)
    (hG : CFSG.Open.IsQuasisimple G) (hpS : p ∣ Nat.card ρ.range)
    (hno : NoAp p (G ⧸ Subgroup.center G)) :
    ∃ X : Subgroup Y, X ≤ J ∧ CFSG.Open.IsQuasisimple ↥X ∧ p ∣ Nat.card X ∧
      ∀ φ : ↥X →* alternatingGroup (Fin p), ¬ φ.ker ≤ Subgroup.center ↥X := by
  classical
  set S : Subgroup (↥L ⧸ Subgroup.center ↥L) := ρ.range with hSdef
  set π : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hπ
  have hkerπ : π.ker ≤ Subgroup.center ↥L := by rw [hπ, QuotientGroup.ker_mk']
  have hGperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := hG.1
  have hS : ⁅S, S⁆ = S := by
    have h1 : S = (⊤ : Subgroup G).map ρ := by rw [hSdef, MonoidHom.range_eq_map]
    rw [h1, ← Subgroup.map_commutator, hGperf]
  have hrange : S ≤ π.range := by
    rw [MonoidHom.range_eq_top_of_surjective π (QuotientGroup.mk'_surjective _)]
    exact le_top
  obtain ⟨W, hW, hWle, hWmap⟩ := ParabPrime.exists_perfect_map_eq π hkerπ hS hrange
  have hWJ : ∀ w ∈ W, (w : Y) ∈ J := by
    intro w hw
    have h1 : π w ∈ S := hWle hw
    obtain ⟨l, hlJ, hl⟩ := mem_quotImage.1 (hρJ h1)
    have hz : l⁻¹ * w ∈ Subgroup.center ↥L := hkerπ (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπ, QuotientGroup.mk'_apply, hl]
      simp [hπ])
    have e1 : (w : Y) = (l : Y) * ((l⁻¹ * w : ↥L) : Y) := by simp
    rw [e1]
    exact J.mul_mem hlJ (hZ _ hz)
  let f : ↥W →* ↥S := (π.comp W.subtype).codRestrict S (fun w => hWle w.2)
  have hf : Function.Surjective f := by
    intro s
    have hs : (s : ↥L ⧸ Subgroup.center ↥L) ∈ W.map π := by rw [hWmap]; exact s.2
    obtain ⟨w, hw, hws⟩ := hs
    exact ⟨⟨w, hw⟩, Subtype.ext hws⟩
  have hker_f : f.ker ≤ Subgroup.center ↥W := by
    intro w hw
    have hw1 : π (w : ↥L) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hw)
    have hc : (w : ↥L) ∈ Subgroup.center ↥L := hkerπ (MonoidHom.mem_ker.2 hw1)
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro v
    exact Subtype.ext (hc v)
  have hWperf : ⁅(⊤ : Subgroup ↥W), (⊤ : Subgroup ↥W)⁆ = ⊤ := by
    have h1 : (commutator ↥W).map W.subtype = ⁅W, W⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
        Subgroup.range_subtype]
    rw [hW] at h1
    have h2 : (⊤ : Subgroup ↥W).map W.subtype = W := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    exact Subgroup.map_injective W.subtype_injective (h1.trans h2.symm)
  obtain ⟨eW⟩ := quotCenter_mulEquiv f hf hker_f hWperf
  obtain ⟨eG⟩ := quotCenter_mulEquiv ρ.rangeRestrict (fun s => by
      obtain ⟨g, hg⟩ := s.2
      exact ⟨g, Subtype.ext hg⟩)
    (fun g hg => hker (by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hg)
      exact MonoidHom.mem_ker.2 this)) hGperf
  let e' : ↥W ⧸ Subgroup.center ↥W ≃* G ⧸ Subgroup.center G := eW.trans eG.symm
  have hWq : CFSG.Open.IsQuasisimple ↥W := by
    refine ⟨hWperf, ?_⟩
    have := hG.2
    exact e'.isSimpleGroup
  set X : Subgroup Y := W.map L.subtype with hX
  let eX : ↥W ≃* ↥X := Subgroup.equivMapOfInjective W L.subtype L.subtype_injective
  refine ⟨X, ?_, isQuasisimple_of_mulEquiv eX hWq, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hWJ w hw
  · have h1 : Nat.card X = Nat.card W := (Nat.card_congr eX.toEquiv).symm
    rw [h1]
    refine hpS.trans ?_
    have := Subgroup.card_ker_mul_card_range f
    rw [MonoidHom.range_eq_top_of_surjective f hf, Subgroup.card_top] at this
    exact ⟨Nat.card f.ker, by rw [← this, mul_comm]⟩
  · intro φ hφ
    set φ' : ↥W →* alternatingGroup (Fin p) := φ.comp eX.toMonoidHom with hφ'
    have hker' : φ'.ker ≤ Subgroup.center ↥W := by
      intro w hw
      have h1 : eX w ∈ φ.ker := hw
      have h2 := hφ h1
      rw [Subgroup.mem_center_iff]
      intro v
      have := Subgroup.mem_center_iff.1 h2 (eX v)
      exact eX.injective (by simpa using this)
    let g : ↥W ⧸ φ'.ker →* ↥W ⧸ Subgroup.center ↥W :=
      QuotientGroup.map φ'.ker (Subgroup.center ↥W) (MonoidHom.id _) (by simpa using hker')
    let r : ↥φ'.range ≃* ↥W ⧸ φ'.ker := (QuotientGroup.quotientKerEquivRange φ').symm
    have hg : Function.Surjective (e'.toMonoidHom.comp (g.comp r.toMonoidHom)) := by
      intro s
      obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (e'.symm s)
      refine ⟨r.symm (QuotientGroup.mk w), ?_⟩
      have h1 : g (r (r.symm (QuotientGroup.mk w))) =
          (QuotientGroup.mk w : ↥W ⧸ Subgroup.center ↥W) := by
        rw [MulEquiv.apply_symm_apply]; rfl
      change e' (g (r (r.symm (QuotientGroup.mk w)))) = s
      rw [h1, hw, MulEquiv.apply_symm_apply]
    exact hno ↥φ'.range φ'.range.subtype (Subtype.val_injective)
      (e'.toMonoidHom.comp (g.comp r.toMonoidHom)) hg

end CFSG.AGLEmbedding.LieOut
