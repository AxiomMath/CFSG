module

public import CFSG.LargeExtraspecial.S14Seven
public import CFSG.LargeExtraspecial.OfFStar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial.S4
open scoped commutatorElement

@[expose] def NQIrredStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O)
    (c : Config), Stage S g t → c.Occurs S g t → IsExtraspecialPGroup 2 (Nbar S g t) →
      c ≠ .omegaPlus8b → c ≠ .omegaPlus6 → ∀ D : Subgroup S.O, zpowers t ≤ D →
        D ≤ Nbar S g t → (∀ r ∈ Rbar S g t, ∀ d ∈ D, r * d * r⁻¹ ∈ D) →
          D = zpowers t ∨ D = Nbar S g t

@[expose] def Claim14_9Plus6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
    Stage S g t → Config.omegaPlus6.Occurs S g t → IsExtraspecialPGroup 2 (Nbar S g t) →
      IsSimpleGroup (Mbar0 S) → Concl14_7 S g t → Rbar S g t ≤ (Mbar0 S).map S.Mbar.subtype →
        FCt S t = Nbar S g t

theorem commutator_ne_of_isPGroup {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) {N : Subgroup P} (hN : N ≠ ⊥) : ⁅N, ⊤⁆ ≠ N := by
  intro h
  have : Group.IsNilpotent P := hP.isNilpotent
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp this
  have hle : ∀ k, N ≤ (⊤ : Subgroup P).lowerCentralSeries k := by
    intro k
    induction k with
    | zero => exact le_top
    | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ, ← h]
      exact commutator_mono ih le_rfl
  exact hN (eq_bot_iff.mpr (hn ▸ hle n))

theorem commutator_ne_of_le {X : Type*} [Group X] {p : ℕ} [Fact p.Prime] {N F : Subgroup X}
    [Finite F] (hF : IsPGroup p F) (hNF : N ≤ F) (hN : N ≠ ⊥) : ⁅N, F⁆ ≠ N := by
  intro hDe
  set N₀ := N.subgroupOf F
  have hN₀ : N₀.map F.subtype = N := by
    rw [subgroupOf_map_subtype, inf_of_le_left hNF]
  have hN₀1 : N₀ ≠ ⊥ := by
    intro h
    apply hN
    rw [← hN₀, h, Subgroup.map_bot]
  apply commutator_ne_of_isPGroup hF hN₀1
  apply map_injective F.subtype_injective
  rw [map_commutator, hN₀, ← MonoidHom.range_eq_map, range_subtype, hDe]

theorem conj_mem_commutator {X : Type*} [Group X] {N F : Subgroup X} {r : X}
    (hN : ∀ n ∈ N, r * n * r⁻¹ ∈ N) (hF : ∀ f ∈ F, r * f * r⁻¹ ∈ F) {d : X}
    (hd : d ∈ ⁅N, F⁆) : r * d * r⁻¹ ∈ ⁅N, F⁆ := by
  have e1 : N.map (MulAut.conj r).toMonoidHom ≤ N :=
    map_le_iff_le_comap.mpr fun n hn => hN n hn
  have e2 : F.map (MulAut.conj r).toMonoidHom ≤ F :=
    map_le_iff_le_comap.mpr fun f hf => hF f hf
  have h1 : (⁅N, F⁆).map (MulAut.conj r).toMonoidHom ≤ ⁅N, F⁆ := by
    rw [map_commutator]
    exact commutator_mono e1 e2
  exact h1 ⟨d, hd, rfl⟩

theorem exists_comm_eq_of_extraspecial {X : Type*} [Group X] {N : Subgroup X}
    (hN : IsExtraspecialPGroup 2 N) {t : X} (htN : t ∈ N) (ht1 : t ≠ 1)
    (htc : ∀ y ∈ N, t * y = y * t) : ∃ a ∈ N, ∃ b ∈ N, a * b * a⁻¹ * b⁻¹ = t := by
  obtain ⟨a, b, hab⟩ : ∃ a b : N, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hc : commutator N = ⊥ := (commutator_eq_bot_iff _).mpr ⟨⟨fun a b => hcon a b⟩⟩
    have h2 := hN.2.2.2
    rw [← hN.2.1, hc, card_bot] at h2
    exact absurd h2 (by norm_num)
  have htc' : (⟨t, htN⟩ : N) ∈ center N := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (htc y y.2).symm
  have h1 : ⁅a, b⁆ ≠ 1 := fun h => hab (commutatorElement_eq_one_iff_mul_comm.mp h)
  have h2 := CFSG.RankThree.Literature.FSmith.eq_of_mem_center hN
    (CFSG.RankThree.Literature.FSmith.commutatorElement_mem_center hN a b) htc' h1
    (fun e => ht1 (congrArg Subtype.val e))
  refine ⟨a, a.2, b, b.2, ?_⟩
  have := congrArg Subtype.val h2
  simpa [commutatorElement_def] using this

theorem conj_mem_map_fstar {X : Type*} [Group X] (K : Subgroup X) {r f : X} (hr : r ∈ K)
    (hf : f ∈ (timmesfeldFStar K).map K.subtype) :
    r * f * r⁻¹ ∈ (timmesfeldFStar K).map K.subtype := by
  obtain ⟨f, hf, rfl⟩ := hf
  exact ⟨⟨r, hr⟩ * f * ⟨r, hr⟩⁻¹,
    (CFSG.LargeExtraspecial.timmesfeldFStar_normal K).conj_mem f hf _, rfl⟩

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem Nbar_le_Ct (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} : Nbar S g t ≤ Ct S t := fun _ hn =>
  ⟨Rbar_le_Mbar (Nbar_le_Rbar hn), mem_centralizer_singleton_iff.mpr
    (commute_of_mem_Rbar haQ (Nbar_le_Rbar hn))⟩

theorem conj_mem_Nbar_of_mem_Ct (haQ : g * S.z * g⁻¹ ∈ S.QG) {t c n : S.O} (hc : c ∈ Ct S t)
    (hn : n ∈ Nbar S g t) : c * n * c⁻¹ ∈ Nbar S g t := by
  obtain ⟨k, hk⟩ : ∃ k : S.M, S.ρ k = c := hc.1
  have hkt : S.ρ k * t = t * S.ρ k := by
    rw [hk]
    exact mem_centralizer_singleton_iff.mp hc.2
  have := conj_mem_Nbar haQ hkt hn
  rwa [hk] at this

theorem Nbar_le_FCt (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (hN2 : IsPGroup 2 (Nbar S g t)) :
    Nbar S g t ≤ FCt S t := by
  have hNC := Nbar_le_Ct (S := S) (g := g) haQ (t := t)
  set N' := (Nbar S g t).subgroupOf (Ct S t) with hN'
  have hN'n : N'.Normal := by
    refine ⟨fun n hn c => ?_⟩
    rw [hN', mem_subgroupOf] at hn ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using conj_mem_Nbar_of_mem_Ct haQ c.2 hn
  have hN'2 : IsPGroup 2 N' := hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNC).symm
  have hN'F : N' ≤ timmesfeldFStar (Ct S t) := by
    have h1 := CFSG.ComponentClassification.PrimeCore.maximal 2 N' hN'2
    have h2 : CFSG.ComponentClassification.PrimeCore.subgroup 2 (Ct S t) ≤
        CFSG.ComponentClassification.Fitting.subgroup (Ct S t) := by
      rw [CFSG.ComponentClassification.PrimeCore.fitting_eq_join]
      exact le_iSup (fun p : {p : ℕ // p.Prime} =>
        CFSG.ComponentClassification.PrimeCore.subgroup p.val (Ct S t)) ⟨2, Nat.prime_two⟩
    exact h1.trans (h2.trans le_sup_left)
  exact fun n hn => ⟨⟨n, hNC hn⟩, hN'F (mem_subgroupOf.mpr hn), rfl⟩

theorem conj_mem_FCt (haQ : g * S.z * g⁻¹ ∈ S.QG) {t r f : S.O} (hr : r ∈ Rbar S g t)
    (hf : f ∈ FCt S t) : r * f * r⁻¹ ∈ FCt S t :=
  conj_mem_map_fstar (Ct S t) ⟨Rbar_le_Mbar hr, Rbar_le_centralizer haQ hr⟩ hf

theorem claim14_9_of (hirr : NQIrredStmt) (h6 : Claim14_9Plus6) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O)
      (c : Config), Stage S g t → c.Occurs S g t → IsExtraspecialPGroup 2 (Nbar S g t) →
        IsSimpleGroup (Mbar0 S) → Concl14_7 S g t → Rbar S g t ≤ (Mbar0 S).map S.Mbar.subtype →
          FCt S t = Nbar S g t ∨ c = .omegaPlus8b := by
  intro G _ _ _ S g t c hSt hocc hext hsim h7 h8
  by_cases hc8 : c = .omegaPlus8b
  · exact Or.inr hc8
  left
  by_cases hc6 : c = .omegaPlus6
  · subst hc6
    exact h6 G S g t hSt hocc hext hsim h7 h8
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haQ := hSt.hyp4.conj_mem
  have ht1 := hSt.ne_one
  have htN := S6.self_mem_Nbar hSt.hyp4 hSt.mem
  have hNF := Nbar_le_FCt haQ hext.1
  have hFC : FCt S t ≤ Ct S t := map_subtype_le _
  have hF2 : IsPGroup 2 (FCt S t) := h7.2.map _
  have hDN : ⁅Nbar S g t, FCt S t⁆ ≤ Nbar S g t := commutator_le.mpr fun n hn f hf => by
    have e : ⁅n, f⁆ = n * (f * n⁻¹ * f⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem hn (conj_mem_Nbar_of_mem_Ct haQ (hFC hf) (inv_mem hn))
  have htD : zpowers t ≤ ⁅Nbar S g t, FCt S t⁆ := by
    rw [zpowers_le]
    obtain ⟨a, ha, b, hb, hab⟩ := exists_comm_eq_of_extraspecial hext htN ht1 fun y hy =>
      (commute_of_mem_Rbar haQ (Nbar_le_Rbar hy)).symm
    have := commutator_mem_commutator ha (hNF hb)
    rwa [commutatorElement_def, hab] at this
  have hDR : ∀ r ∈ Rbar S g t, ∀ d ∈ ⁅Nbar S g t, FCt S t⁆, r * d * r⁻¹ ∈ ⁅Nbar S g t, FCt S t⁆ :=
    fun r hr _ hd => conj_mem_commutator (fun _ hn => conj_mem_Nbar_of_mem_Rbar haQ hr hn)
      (fun _ hf => conj_mem_FCt haQ hr hf) hd
  have hN1 : Nbar S g t ≠ ⊥ := fun h => ht1 (by rwa [h, mem_bot] at htN)
  rcases hirr G S g t c hSt hocc hext hc8 hc6 _ htD hDN hDR with hDt | hDe
  · refine le_antisymm (fun f hf => h7.1 f (hFC hf).1 fun y hy => ?_) hNF
    rw [← hDt]
    have := commutator_mem_commutator hy hf
    rw [commutatorElement_def] at this
    have e : f * y * f⁻¹ * y⁻¹ = (y * f * y⁻¹ * f⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem this
  · exact absurd hDe (commutator_ne_of_le hF2 hNF hN1)

end CFSG.LargeExtraspecial.S14
