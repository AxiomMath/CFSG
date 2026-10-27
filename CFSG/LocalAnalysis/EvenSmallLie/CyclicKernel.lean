module

public import CFSG.LocalAnalysis.EvenSmallLie.Children
public import CFSG.LocalAnalysis.EvenSmallLie.FoursGroup
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionKernel
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelBasic
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Local

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie

open Subgroup CFSG.Open CFSG.ComponentClassification M12Cover.CyclicKernel

@[expose] def FoursGroupCondition (L : Type*) [Group L] : Prop :=
  ∀ φ : MulAut L, φ * φ = 1 → (∀ m : L, φ ≠ MulAut.conj m) →
    ∃ l : L, (l * (φ l)⁻¹) ^ 2 = 1 ∧ l * (φ l)⁻¹ ∉ center L

theorem FoursGroupCondition.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : FoursGroupCondition X) : FoursGroupCondition Y := by
  intro φ hφ hout
  set ψ : MulAut X := (MulAut.congr e).symm φ with hψdef
  have hψ : ∀ x : X, e (ψ x) = φ (e x) := fun x => by simp [hψdef]
  have hψψ : ψ * ψ = 1 := by rw [hψdef, ← map_mul, hφ, map_one]
  have hψout : ∀ m : X, ψ ≠ MulAut.conj m := by
    intro m hm
    apply hout (e m)
    ext y
    have h1 := hψ (e.symm y)
    rw [hm, MulEquiv.apply_symm_apply, MulAut.conj_apply] at h1
    rw [← h1, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  obtain ⟨l, hl1, hl2⟩ := h ψ hψψ hψout
  have hel : e l * (φ (e l))⁻¹ = e (l * (ψ l)⁻¹) := by rw [map_mul, map_inv, hψ]
  refine ⟨e l, by rw [hel, ← map_pow, hl1, map_one], fun hc => hl2 ?_⟩
  rw [hel, mem_center_iff] at hc
  rw [mem_center_iff]
  intro g
  apply e.injective
  have h1 := hc (e g)
  rwa [← map_mul, ← map_mul] at h1

theorem FoursGroupCondition.of_forall_eq_conj {L : Type*} [Group L]
    (h : ∀ φ : MulAut L, ∃ m, φ = MulAut.conj m) : FoursGroupCondition L :=
  fun φ _ hout => absurd (h φ).choose_spec (hout _)

open CFSG.ComponentClassification.PerfectAutomorphisms in
theorem FoursGroupCondition.of_forall_eq_conj_quotient {L : Type*} [Group L] [Group.IsPerfect L]
    (h : ∀ α : MulAut (L ⧸ center L), ∃ q, α = MulAut.conj q) : FoursGroupCondition L := by
  refine FoursGroupCondition.of_forall_eq_conj fun φ => ?_
  obtain ⟨q, hq⟩ := h (centerQuotientHom L φ)
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨m, centerQuotientHom_injective L ?_⟩
  rw [hq]
  ext x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  change _ = onCenterQuotient (MulAut.conj m) (QuotientGroup.mk' (center L) x)
  rw [onCenterQuotient_apply_mk, MulAut.conj_apply, MulAut.conj_apply]
  rfl

section Small

variable {G : Type} [Group G] [Finite G]

theorem false_of_forall_card_le_two [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {L : Subgroup G} (hL : standardComponentIsStandard L)
    (hcore : ∀ x : G, orderOf x = 2 →
      standardComponentOddCore (centralizer ({x} : Set G)) = ⊥)
    (hFG : FoursGroupCondition L) (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G)))) (hS4 : 4 ≤ Nat.card S)
    (hsmall : ∀ g : G, g ∉ normalizer (L : Set G) → ∀ P : Subgroup G,
      P ≤ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓ normalizer (L : Set G) →
      IsPGroup 2 P → Nat.card P ≤ 2) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (L : Set G) with hNdef
  set S₀ : Subgroup G :=
    (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype with hS₀def
  obtain ⟨σ, hσS, hσ4⟩ := exists_orderOf_eq_four_of_isCyclic hS S.isPGroup' (by omega)
  set s : G := (σ : G) with hsdef
  have hs4 : orderOf s = 4 := by rw [hsdef, orderOf_coe, hσ4]
  have hsC : s ∈ centralizer (L : Set G) := σ.2
  have hsS₀ : s ∈ S₀ := ⟨σ, hσS, rfl⟩
  set tC : centralizer (L : Set G) := σ ^ 2 with htCdef
  have htCS : tC ∈ (S : Subgroup (centralizer (L : Set G))) := pow_mem hσS 2
  have htC2 : orderOf tC = 2 := by
    rw [htCdef, orderOf_pow_of_dvd (by norm_num) (by rw [hσ4]; norm_num), hσ4]
  set t : G := (tC : G) with htdef
  have hts : t = s ^ 2 := by rw [htdef, htCdef, coe_pow]
  have ht2 : orderOf t = 2 := by rw [htdef, orderOf_coe, htC2]
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := fun h => by simp [h] at ht2
  have htC : t ∈ centralizer (L : Set G) := tC.2
  have htS₀ : t ∈ S₀ := ⟨tC, htCS, rfl⟩
  obtain ⟨-, -, hLH, -, -, -, hCH, -, -⟩ :=
    StandardRecognition.standard_cyclic_local_centralizer_kernel hL S hS htCS htC2 (hcore t ht2)
  set H := centralizer ({t} : Set G) with hHdef
  replace hCH : centralizer (L : Set G) ⊓ H = S₀ := hCH
  have hHN : H ≤ N := centralizer_le_normalizer_of_standard hL htC ht2
  have hS₀cyc : IsCyclic S₀ := isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)
  have hS₀ab : ∀ a ∈ S₀, ∀ b ∈ S₀, a * b = b * a := fun a ha b hb =>
    mul_comm_of_isCyclic hS₀cyc ha hb
  set M := centralizer ({s} : Set G) with hMdef
  have hLM : L ≤ M := fun l hl =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hsC l hl)
  have hS₀M : S₀ ≤ M := fun x hx => mem_centralizer_singleton_iff.mpr (hS₀ab x hx s hsS₀)
  have htM : t ∈ M := hS₀M htS₀
  have hMH : M ≤ H := fun x hx => by
    rw [hHdef, mem_centralizer_singleton_iff, hts]
    exact (Commute.pow_right (mem_centralizer_singleton_iff.mp hx) 2).eq
  have hdich : ∀ h ∈ H, h ∈ M ∨ h * s * h⁻¹ = s⁻¹ := by
    intro h hh
    have hc1 : Commute h t := mem_centralizer_singleton_iff.mp hh
    have hc2 : Commute s t := by
      rw [hts]
      exact Commute.self_pow s 2
    have hmem : h * s * h⁻¹ ∈ S₀ := by
      rw [← hCH]
      exact ⟨conj_mem_centralizer_of_mem_normalizer (hHN hh) hsC,
        mem_centralizer_singleton_iff.mpr ((hc1.mul_left hc2).mul_left hc1.inv_left)⟩
    rcases eq_or_eq_inv_of_orderOf_eq_four hS₀cyc hsS₀ hmem hs4
      (by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hs4]) with h1 | h1
    · left
      rw [hMdef, mem_centralizer_singleton_iff]
      calc h * s = h * s * h⁻¹ * h := by group
        _ = s * h := by rw [h1]
    · exact Or.inr h1
  have key : ∀ y ∈ H, IsConj t y → y ≠ t → y ∉ M := by
    intro y hyH hy hyt hyM
    obtain ⟨g, rfl⟩ := isConj_iff.mp hy
    by_cases hg : g ∈ N
    · apply hyt
      have hyS : g * t * g⁻¹ ∈ S₀ :=
        hCH ▸ ⟨conj_mem_centralizer_of_mem_normalizer hg htC, hyH⟩
      exact eq_of_orderOf_eq_two_of_isCyclic hS₀cyc hyS htS₀
        (by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht2]) ht2
    · have hg' : g⁻¹ ∉ N := fun h => hg (by simpa using inv_mem h)
      have hsg : orderOf (g⁻¹ * s * g) = 4 := by
        rw [show g⁻¹ * s * g = MulAut.conj g⁻¹ s by simp,
          MulEquiv.orderOf_eq, hs4]
      have hP := hsmall g⁻¹ hg' (zpowers (g⁻¹ * s * g)) ?_
        (IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hsg]; norm_num))
      · rw [Nat.card_zpowers, hsg] at hP
        omega
      · rw [zpowers_le]
        refine ⟨⟨s, hsC, by simp⟩, hHN ?_⟩
        rw [hHdef, mem_centralizer_singleton_iff]
        have h1 := mem_centralizer_singleton_iff.mp hyM
        calc g⁻¹ * s * g * t = g⁻¹ * (s * (g * t * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * t * g⁻¹) * s) * g := by rw [← h1]
          _ = t * (g⁻¹ * s * g) := by group
  have hconjt : ∀ e ∈ H, IsConj t e → e ≠ t → IsConj (t * e) e := by
    intro e heH he het
    have h1 : e * s * e⁻¹ = s⁻¹ := (hdich e heH).resolve_left (key e heH he het)
    refine (isConj_iff.mpr ⟨s, ?_⟩).symm
    calc s * e * s⁻¹ = s * (e * s * e⁻¹)⁻¹ * e := by group
      _ = t * e := by rw [h1, inv_inv, hts, sq]
  have hM : ∀ y ∈ M, IsConj t y → y = t := by
    intro y hyM hy
    by_contra hyt
    exact key y (hMH hyM) hy hyt hyM
  have hindex : M.relIndex H ≤ 2 := by
    refine (LocalAnalysis.ComponentInitial.Finkelstein1977.normal_index_le_two_of_mul_mem
      (H := M.subgroupOf H) fun a b ha hb => ?_).2
    rw [mem_subgroupOf] at ha hb ⊢
    have ha' := (hdich a a.2).resolve_left ha
    have hb' := (hdich b b.2).resolve_left hb
    rw [hMdef, mem_centralizer_singleton_iff, coe_mul]
    calc (a : G) * b * s = a * (b * s * (b : G)⁻¹) * (a : G)⁻¹ * (a * b) := by group
      _ = (a * s * (a : G)⁻¹)⁻¹ * (a * b) := by rw [hb']; group
      _ = s * (a * b) := by rw [ha', inv_inv]
  have hV : ∀ y ∈ H, y ∉ M → IsConj t y → ∃ V : Subgroup G, Nat.card V = 4 ∧
      V ≤ centralizer ({y} : Set G) ∧ ∀ v ∈ V, v ≠ 1 → IsConj (v * y) y := by
    intro y hyH hyM hy
    have hyt : y ≠ t := fun h => hyM (h ▸ htM)
    have hy2 : y * y = 1 := by
      obtain ⟨c, rfl⟩ := isConj_iff.mp hy
      calc c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
        _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    have hty : Commute t y := (mem_centralizer_singleton_iff.mp hyH).symm
    set φ : MulAut L := L.normalizerMonoidHom ⟨y, hHN hyH⟩ with hφdef
    have hφ : ∀ x : L, ((φ x : L) : G) = y * x * y⁻¹ := fun x => rfl
    have hφφ : φ * φ = 1 := by
      rw [hφdef, ← map_mul]
      convert map_one L.normalizerMonoidHom
      exact Subtype.ext hy2
    have hφout : ∀ m : L, φ ≠ MulAut.conj m := by
      intro m hm
      apply hyM
      have hc : (m : G)⁻¹ * y ∈ centralizer (L : Set G) := by
        rw [mem_centralizer_iff]
        intro x hx
        have h1 : y * x * y⁻¹ = m * x * (m : G)⁻¹ := by
          have := congrArg (fun f : MulAut L => ((f ⟨x, hx⟩ : L) : G)) hm
          simpa [hφ, MulAut.conj_apply] using this
        calc x * ((m : G)⁻¹ * y) = (m : G)⁻¹ * (m * x * (m : G)⁻¹) * y := by group
          _ = (m : G)⁻¹ * (y * x * y⁻¹) * y := by rw [h1]
          _ = (m : G)⁻¹ * y * x := by group
      have hcS : (m : G)⁻¹ * y ∈ S₀ := by
        rw [← hCH]
        exact ⟨hc, H.mul_mem (H.inv_mem (hLH m.2)) hyH⟩
      have hy' : y = m * ((m : G)⁻¹ * y) := by group
      rw [hy']
      exact mul_mem (hLM m.2) (hS₀M hcS)
    obtain ⟨l, hl1, hl2⟩ := hFG φ hφφ hφout
    obtain ⟨w, hwdef⟩ : ∃ w : L, w = l * (φ l)⁻¹ := ⟨_, rfl⟩
    rw [← hwdef] at hl1 hl2
    have hw2 : (w : G) * w = 1 := by rw [← coe_mul, ← sq, hl1, coe_one]
    have hwinv : (w : G)⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    have hw : (w : G) = l * y * (l : G)⁻¹ * y⁻¹ := by
      rw [hwdef, coe_mul, coe_inv, hφ]
      group
    have hwy : (w : G) * y = l * y * (l : G)⁻¹ := by rw [hw]; group
    have hwc : Commute (w : G) y := by
      show (w : G) * y = y * w
      calc (w : G) * y = l * y * (l : G)⁻¹ := hwy
        _ = (y * y) * l * y⁻¹ * (l : G)⁻¹ := by rw [hy2, one_mul, hyinv]
        _ = y * (w : G)⁻¹ := by rw [hw]; group
        _ = y * w := by rw [hwinv]
    have hw1 : (w : G) ≠ 1 := fun h => hl2 (by
      rw [show w = 1 from Subtype.ext h]
      exact one_mem _)
    have htw : t ≠ (w : G) := fun h => hl2 (by
      rw [mem_center_iff]
      intro g
      apply Subtype.ext
      rw [coe_mul, coe_mul, ← h]
      exact mem_centralizer_iff.mp htC g g.2)
    have hwyconj : IsConj ((w : G) * y) y := (isConj_iff.mpr ⟨(l : G), hwy.symm⟩).symm
    have htwy : IsConj (t * w * y) y := by
      have heH : (w : G) * y ∈ H := by
        rw [hwy]
        exact mul_mem (mul_mem (hLH l.2) hyH) (inv_mem (hLH l.2))
      have het : (w : G) * y ≠ t := by
        intro h
        apply hyt
        have h1 : (l : G) * y * (l : G)⁻¹ = t := hwy.symm.trans h
        have hlt : (l : G) * t = t * l := mem_centralizer_singleton_iff.mp (hLH l.2)
        calc y = (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹) * l := by group
          _ = (l : G)⁻¹ * t * l := by rw [h1]
          _ = (l : G)⁻¹ * ((l : G) * t) := by rw [hlt]; group
          _ = t := by group
      rw [mul_assoc]
      exact (hconjt _ heH (hy.trans hwyconj.symm) het).trans hwyconj
    obtain ⟨V, -, hV4, hVy, hVconj⟩ := exists_four_of_pair (N := ⊤) (y := y) htt hw2
      (mem_centralizer_iff.mp htC w w.2).symm ht1 hw1 htw (by
        rintro x (rfl | rfl | rfl)
        · exact ⟨mem_top _, hty, hconjt y hyH hy hyt⟩
        · exact ⟨mem_top _, hwc, hwyconj⟩
        · exact ⟨mem_top _, hty.mul_left hwc, htwy⟩)
    exact ⟨V, hV4, hVy, hVconj⟩
  exact false_of_fours_group hnonab ht2 htM hindex hM hV

theorem StandardSetting.isCyclic_sylow {L : Subgroup G} (hset : StandardSetting G L)
    (S : Sylow 2 (centralizer (L : Set G))) :
    IsCyclic (S : Subgroup (centralizer (L : Set G))) := by
  obtain ⟨S', hS'⟩ := hset.cyclic
  exact (Sylow.equiv S S').isCyclic.mpr hS'

theorem StandardSetting.false_of_forall_card_le_two {L : Subgroup G}
    (hset : StandardSetting G L) (hFG : FoursGroupCondition L)
    (S : Sylow 2 (centralizer (L : Set G))) (hS4 : 4 ≤ Nat.card S)
    (hsmall : ∀ g : G, g ∉ normalizer (L : Set G) → ∀ P : Subgroup G,
      P ≤ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓ normalizer (L : Set G) →
      IsPGroup 2 P → Nat.card P ≤ 2) : False :=
  haveI := hset.simple
  CFSG.EvenSmallLie.false_of_forall_card_le_two hset.nonab hset.standard hset.core hFG S
    (hset.isCyclic_sylow S) hS4 hsmall

end Small

end CFSG.EvenSmallLie
