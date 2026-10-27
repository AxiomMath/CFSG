module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiPiece
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiLu
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapSW2EightAux
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapSW2EightLayer

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

section Eight

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))} {s : X}

private theorem bcdEight_normalizes_E {Zs B : Subgroup X} {u : X}
    (huN : u ∈ normalizer (Zs : Set X)) (huB : u ∈ normalizer (B : Set X)) :
    u ∈ normalizer (oTwoPrimeOf (B ⊓ centralizer (Zs : Set X)) : Set X) := by
  have hCZ : u ∈ normalizer ((centralizer (Zs : Set X) : Subgroup X) : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : ∀ y : X, y ∈ normalizer (Zs : Set X) → ∀ x : X, x ∈ centralizer (Zs : Set X) →
        y * x * y⁻¹ ∈ centralizer (Zs : Set X) := by
      intro y hy x hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : y⁻¹ * z * y ∈ Zs := by
        have := (Subgroup.mem_normalizer_iff.1 ((normalizer (Zs : Set X)).inv_mem hy) z).1 hz
        simpa using this
      have hxc := Subgroup.mem_centralizer_iff.1 hx (y⁻¹ * z * y) hz'
      calc z * (y * x * y⁻¹) = y * ((y⁻¹ * z * y) * x) * y⁻¹ := by group
        _ = y * (x * (y⁻¹ * z * y)) * y⁻¹ := by rw [hxc]
        _ = y * x * y⁻¹ * z := by group
    refine ⟨fun hx => key u huN x hx, fun hx => ?_⟩
    have := key u⁻¹ ((normalizer (Zs : Set X)).inv_mem huN) _ hx
    simpa [mul_assoc] using this
  exact oTwoPrimeOf_normalizes (A := Subgroup.zpowers u) (H := B ⊓ centralizer (Zs : Set X))
    ((Subgroup.zpowers_le).2 (mem_normalizer_inf huB hCZ)) (Subgroup.mem_zpowers u)

private theorem bcdEight_exists_cent {D : Subgroup X} (Λ : Subgroup ↥D) [Λ.Normal] :
    ∃ Ĉ : Subgroup ↥D, Ĉ.Normal ∧
      ∀ c : ↥D, c ∈ Ĉ ↔ ∀ x ∈ Λ, ⁅(x : X), (c : X)⁆ ∈ oddCoreOf D := by
  classical
  set π : ↥D →* ↥D ⧸ pPrimeCore 2 ↥D := QuotientGroup.mk' (pPrimeCore 2 ↥D) with hπ
  haveI : (Λ.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  refine ⟨(Subgroup.centralizer ((Λ.map π : Subgroup (↥D ⧸ pPrimeCore 2 ↥D)) :
    Set (↥D ⧸ pPrimeCore 2 ↥D))).comap π, inferInstance, fun c => ?_⟩
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff_commutator_eq_one]
  constructor
  · intro hc x hx
    have h1 : ⁅π x, π c⁆ = 1 := hc (π x) (Subgroup.mem_map_of_mem π hx)
    have h2 : π ⁅x, c⁆ = 1 := by rw [map_commutatorElement]; exact h1
    have h3 : (⁅x, c⁆ : ↥D) ∈ pPrimeCore 2 ↥D := (QuotientGroup.eq_one_iff _).1 h2
    exact mem_oddCoreOf_iff.2 ⟨(⁅x, c⁆ : ↥D).2, h3⟩
  · intro hc g hg
    obtain ⟨x, hx, rfl⟩ := hg
    obtain ⟨_hmem, h3⟩ := mem_oddCoreOf_iff.1 (hc x hx)
    have h2 : π ⁅x, c⁆ = 1 := (QuotientGroup.eq_one_iff _).2 h3
    rwa [map_commutatorElement] at h2

private theorem bcdEight_section_of_cover {B B' : Subgroup X} {u : X} (hB'B : B' ≤ B)
    (hcov : B ≤ pPrimeCoreOf 2 B ⊔ B') (huB : u ∈ normalizer (B : Set X))
    (hcomm : ∀ e ∈ B', ⁅e, u⁆ ∈ pPrimeCoreOf 2 B') :
    u ∈ centralizerSection B (pPrimeCoreOf 2 B) := by
  have hcov' : B' ⊔ pPrimeCoreOf 2 B = B :=
    le_antisymm (sup_le hB'B (oddCoreOf_le B)) (by rw [sup_comm]; exact hcov)
  have hOB' : pPrimeCoreOf 2 B' ≤ pPrimeCoreOf 2 B :=
    (pPrimeCoreOf_eq_inf_of_covers hB'B hcov').le.trans inf_le_right
  have huO : u ∈ normalizer (pPrimeCoreOf 2 B : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer huB
  refine ⟨huB, huO, fun b hb => ?_⟩
  have hb' : b ∈ pPrimeCoreOf 2 B ⊔ B' := hcov hb
  obtain ⟨o, ho, e, he, rfl⟩ := (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing
    (pPrimeCoreOf 2 B) B' (fun x hx => le_normalizer_oddCoreOf B (hB'B hx)) b).1 hb'
  have h1 : ⁅o * e, u⁆ = o * ⁅e, u⁆ * o⁻¹ * (o * (u * o⁻¹ * u⁻¹)) := by
    simp only [commutatorElement_def]; group
  rw [h1]
  have h2 : o * ⁅e, u⁆ * o⁻¹ ∈ pPrimeCoreOf 2 B :=
    (pPrimeCoreOf 2 B).mul_mem ((pPrimeCoreOf 2 B).mul_mem ho (hOB' (hcomm e he)))
      ((pPrimeCoreOf 2 B).inv_mem ho)
  have h3 : o * (u * o⁻¹ * u⁻¹) ∈ pPrimeCoreOf 2 B :=
    (pPrimeCoreOf 2 B).mul_mem ho
      ((Subgroup.mem_normalizer_iff.1 huO o⁻¹).1 ((pPrimeCoreOf 2 B).inv_mem ho))
  exact (pPrimeCoreOf 2 B).mul_mem h2 h3

private theorem bcdEight_contra (h : Sec5Data X n z Z S) (hs : IsSec5Inv X Z s) {y u : X}
    (hy2 : y * y = 1) (hys : y * s = s * y) (huZ : u ∈ Z) (hu1 : u ≠ 1) (hus : u * s = s * u)
    (huy : u * y = y * u)
    (hlay : ∀ x ∈ (pLayer ↥(centralizer ({y} : Set X)) 2).map
      (centralizer ({y} : Set X)).subtype, ⁅x, u⁆ ∈ oddCoreOf (centralizer ({y} : Set X)))
    {B : Subgroup X} (hB : Sec5Comp X n (centralizer ({s} : Set X)) B)
    (hyB : y ∈ centralizerSection B (pPrimeCoreOf 2 B)) : False := by
  classical
  have hy2' : y ^ 2 = 1 := by rw [sq]; exact hy2
  have hs2' : s ^ 2 = 1 := by rw [sq]; exact hs.sq
  have hu2 : u * u = 1 := h.Z_sq_eq_one huZ
  have hu2' : u ^ 2 = 1 := by rw [sq]; exact hu2
  have huCs : u ∈ centralizer ({s} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hus
  have huCy : u ∈ centralizer ({y} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 huy
  have huD : u ∈ centralizer ({s} : Set X) ⊓ centralizer ({y} : Set X) := ⟨huCs, huCy⟩
  obtain ⟨⟨u₀, hu₀⟩, hBn⟩ := id hB
  obtain ⟨u', hu', hu'c⟩ := hu₀.exists_witness_centralizer_singleton hy2' hyB
  obtain ⟨hd1, -, hcovB⟩ := hu'.descend_singleton hBn hy2' hyB hu'c
  set B' : Subgroup X := oTwoPrimeOf (B ⊓ centralizer ({y} : Set X)) with hB'
  have hB'pc : IsPCompIn 2 (centralizer ({s} : Set X) ⊓ centralizer ({y} : Set X)) B' :=
    hd1.2.2.1
  have hB'B : B' ≤ B := (oTwoPrimeOf_le _).trans inf_le_left
  have hB'D : B' ≤ centralizer ({s} : Set X) ⊓ centralizer ({y} : Set X) := hB'pc.1
  have hB'q : IsTwoGenQuasi ↥B' :=
    (isTwoGenQuasi_subgroupOf_iff hB'D).1 (isPComponent_two_iff.1 hB'pc.2).2
  have hB'L := le_pLayer_of_isPCompIn_inf hs2' hys.symm hB'pc
  have hcomm : ∀ l ∈ B', ⁅l, u⁆ ∈ pPrimeCoreOf 2
      (centralizer ({s} : Set X) ⊓ centralizer ({y} : Set X)) := by
    intro l hl
    have h1 : ⁅l, u⁆ ∈ oddCoreOf (centralizer ({y} : Set X)) := hlay l (hB'L hl)
    have h2 : ⁅l, u⁆ ∈ centralizer ({s} : Set X) ⊓ centralizer ({y} : Set X) := by
      have hl' := hB'D hl
      simp only [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hl' huD) (inv_mem hl')) (inv_mem huD)
    exact inf_oddCoreOf_le inf_le_right ⟨h2, h1⟩
  have hsecB' : u ∈ centralizerSection B' (pPrimeCoreOf 2 B') :=
    normalizes_isPCompIn_of_comm_mem hB'pc (Subgroup.le_normalizer huD) hcomm
  have huB : u ∈ normalizer (B : Set X) := by
    have hB'u : B'.map (MulAut.conj u).toMonoidHom = B' :=
      map_conj_eq_of_mem_normalizer hsecB'.1
    have hBu : Sec5Comp X n (centralizer ({s} : Set X)) (B.map (MulAut.conj u).toMonoidHom) :=
      hB.map_conj (Subgroup.le_normalizer huCs)
    have hB'Bu : B' ≤ B.map (MulAut.conj u).toMonoidHom :=
      hB'u.symm.le.trans (Subgroup.map_mono hB'B)
    exact mem_normalizer_of_map_conj_eq
      (eq_of_isPCompIn_of_le hBu.isPCompIn hB.isPCompIn hB'Bu hB'B hB'q)
  have hsecB : u ∈ centralizerSection B (pPrimeCoreOf 2 B) :=
    bcdEight_section_of_cover hB'B hcovB huB hsecB'.2.2
  exact K0_ne_bot_of_centralizerSection hu2' hB hsecB (sec5_K0_inf_eq_bot h hs huZ hu1 hus)

private theorem bcdEight_u_cent (h : Sec5Data X n z Z S) (hs : IsSec5Inv X Z s)
    (hzs : z * s = s * z) (hn8 : n = 8) {M : Subgroup X}
    (hM : Sec5Comp X n (centralizer ({z} : Set X)) M)
    (hMs : M.map (MulAut.conj s).toMonoidHom ≠ M) {y : X} (hy2 : y * y = 1) (hy1 : y ≠ 1)
    (hys : y * s = s * y) (hyM : y ∈ normalizer (M : Set X)) (hyZ : y ∈ normalizer (Z : Set X))
    (hfix : fixCount ((AhatModel.ofCover hM.2).perm y hyM) = n - 4)
    (hJ : K0 X n (K0 X n (centralizer ({s} : Set X)) ⊓ centralizer ({y} : Set X)) ≠ ⊥) :
    ∃ u : X, u ∈ Z ∧ u ≠ 1 ∧ u * s = s * u ∧ u * y = y * u ∧
      ∀ x ∈ (pLayer ↥(centralizer ({y} : Set X)) 2).map (centralizer ({y} : Set X)).subtype,
        ⁅x, u⁆ ∈ oddCoreOf (centralizer ({y} : Set X)) := by
  classical
  haveI hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 8 ≤ n := h.maxdeg.1
  obtain ⟨hM₀c, hM₀M, hcovM⟩ := exists_mirror_comp h hM
  set M₀ : Subgroup X := oTwoPrimeOf (M ⊓ centralizer (Z : Set X)) with hM₀def
  obtain ⟨u, hu⟩ := hM₀c.1
  have hu2 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu.1, sq] at this
    exact this
  have hu1 : u ≠ 1 := by
    intro h1
    have := hu.1
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have huZ : u ∈ Z := h.mem_Z_of_comm_mem hM₀c hu.2.1 hu2 (fun a ha => hu.comm_mem a ha)
  have hyM₀ : y ∈ normalizer (M₀ : Set X) := bcdEight_normalizes_E hyZ hyM
  have hzs' : s ∈ centralizer ({z} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hzs.symm
  have hM' : Sec5Comp X n (centralizer ({z} : Set X)) (M.map (MulAut.conj s).toMonoidHom) :=
    hM.map_conj (Subgroup.le_normalizer hzs')
  have hM₀q : IsTwoGenQuasi ↥M₀ :=
    (isTwoGenQuasi_subgroupOf_iff hM₀c.isPCompIn.1).1
      (isPComponent_two_iff.1 hM₀c.isPCompIn.2).2
  have hM₀s : M₀.map (MulAut.conj s).toMonoidHom ≠ M₀ := by
    intro hM₀s
    apply hMs
    have hM₀M' : M₀ ≤ M.map (MulAut.conj s).toMonoidHom :=
      hM₀s.symm.le.trans (Subgroup.map_mono hM₀M)
    exact eq_of_isPCompIn_of_le hM'.isPCompIn hM.isPCompIn hM₀M' hM₀M hM₀q
  have hM₀'c : Sec5Comp X n (normalizer (Z : Set X)) (M₀.map (MulAut.conj s).toMonoidHom) :=
    hM₀c.map_conj (Subgroup.le_normalizer hs.mem)
  have hne : M₀ ≠ M₀.map (MulAut.conj s).toMonoidHom := fun e => hM₀s e.symm
  have hsu : s * u * s⁻¹ = u := swap_witness_eq h hs hM₀c hM₀'c hne rfl hu huZ hu1
  have hus : u * s = s * u := by
    have : s * u = u * s := by
      have := congrArg (fun t => t * s) hsu
      simpa [mul_assoc] using this
    exact this.symm
  have huy : u * y = y * u :=
    Sec5Data.comm_of_mem_Z_of_normalizes h hyZ hM₀c hyM₀ huZ hu.2.1 hu1
  have hperm0 : ((AhatModel.ofCover hM.2).transport hM₀M hcovM).perm y hyM₀ =
      (AhatModel.ofCover hM.2).perm y hyM :=
    (AhatModel.ofCover hM.2).perm_transport hn hM₀M hcovM hyM₀ hyM
  obtain ⟨L, E, hLc, hyL, M', huE, hEML, hcovL, hyE, hperm⟩ :=
    exists_Lu_model h hM₀c huZ hu1 hu hyM₀ huy.symm
      ((AhatModel.ofCover hM.2).transport hM₀M hcovM)
  have hfix4 : fixCount (M'.perm y hyL) = 4 := by
    rw [hperm, hperm0, hfix]
    omega
  have hEL : E ≤ L := fun x hx => (hEML hx).2
  have hEM₀ : E ≤ M₀ := fun x hx => (hEML hx).1
  obtain ⟨Q, hQEC, hQ2, -, huQ, -, ⟨a, haQ, b, hbQ, hab⟩, -, -, -⟩ :=
    exists_sl23_piece hn hu2 hu1 hy2 huy.symm hLc.isPCompIn hEL huE hcovL hyL hyE M'
      (Or.inl hfix4)
  have hQC : Q ≤ centralizer ({y} : Set X) := fun q hq => (hQEC hq).2
  have hQM₀ : Q ≤ M₀ := fun q hq => hEM₀ (hQEC hq).1
  have hsCy : s ∈ centralizer ({y} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hys.symm
  have huCy : u ∈ centralizer ({y} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 huy
  haveI hΛ : (pLayer ↥(centralizer ({y} : Set X)) 2).Normal := by
    haveI := CFSG.ComponentClassification.CatalogueBPrimeJoin.pLayer_characteristic
      (G := ↥(centralizer ({y} : Set X))) (p := 2)
    infer_instance
  obtain ⟨Ĉ, hĈn, hĈ⟩ := bcdEight_exists_cent (D := centralizer ({y} : Set X))
    (pLayer ↥(centralizer ({y} : Set X)) 2)
  have hlay_s := s_centralizes_layer h hs hy2 hy1 hys hJ
  have hsĈ : (⟨s, hsCy⟩ : ↥(centralizer ({y} : Set X))) ∈ Ĉ :=
    (hĈ _).2 fun x hx => hlay_s _ (Subgroup.mem_map_of_mem _ hx)
  set R : Subgroup ↥(centralizer ({y} : Set X)) :=
    (oddCoreOf (normalizer (Z : Set X))).comap (centralizer ({y} : Set X)).subtype with hR
  have hRodd : Odd (Nat.card ↥R) := by
    refine Odd.of_dvd_nat (odd_card_oddCoreOf (normalizer (Z : Set X)))
      (Subgroup.card_dvd_of_injective
        (⟨⟨fun x => ⟨(x.1 : X), x.2⟩, rfl⟩, fun _ _ => rfl⟩ :
          R →* ↥(oddCoreOf (normalizer (Z : Set X)))) ?_)
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun t : ↥(oddCoreOf (normalizer (Z : Set X))) =>
      (t : X)) hab))
  have hQ'2 : IsPGroup 2 ↥(Q.subgroupOf (centralizer ({y} : Set X))) :=
    hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQC).symm
  have haQ' : (⟨a, hQC haQ⟩ : ↥(centralizer ({y} : Set X))) ∈
      Q.subgroupOf (centralizer ({y} : Set X)) := Subgroup.mem_subgroupOf.2 haQ
  have hbQ' : (⟨b, hQC hbQ⟩ : ↥(centralizer ({y} : Set X))) ∈
      Q.subgroupOf (centralizer ({y} : Set X)) := Subgroup.mem_subgroupOf.2 hbQ
  have hab' : ⁅(⟨a, hQC haQ⟩ : ↥(centralizer ({y} : Set X))),
      (⟨s, hsCy⟩ : ↥(centralizer ({y} : Set X))) * ⟨b, hQC hbQ⟩ * (⟨s, hsCy⟩ :
        ↥(centralizer ({y} : Set X)))⁻¹⁆ ∈ R := by
    refine Subgroup.mem_comap.2 ?_
    show ⁅a, s * b * s⁻¹⁆ ∈ oddCoreOf (normalizer (Z : Set X))
    exact commutator_mem_oddCoreOf_of_ne hM₀c.isPCompIn hM₀'c.isPCompIn hne (hQM₀ haQ)
      ⟨b, hQM₀ hbQ, by simp [MulAut.conj_apply]⟩
  have hcomm := comm_mem_of_odd_commutator (Ĉ := Ĉ) hsĈ hQ'2 hRodd haQ' hbQ' hab'
  have huĈ : (⟨u, huCy⟩ : ↥(centralizer ({y} : Set X))) ∈ Ĉ := by
    have hcomm' : (⁅(⟨a, hQC haQ⟩ : ↥(centralizer ({y} : Set X))),
        (⟨b, hQC hbQ⟩ : ↥(centralizer ({y} : Set X)))⁆ : ↥(centralizer ({y} : Set X))) =
        (⟨u, huCy⟩ : ↥(centralizer ({y} : Set X))) := Subtype.ext hab
    rwa [hcomm'] at hcomm
  refine ⟨u, huZ, hu1, hus, huy, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (hĈ _).1 huĈ x hx

private theorem bcdEight_core (h : Sec5Data X n z Z S) (hs : IsSec5Inv X Z s)
    (hzs : z * s = s * z) (hn8 : n = 8) {M : Subgroup X}
    (hM : Sec5Comp X n (centralizer ({z} : Set X)) M)
    (hMs : M.map (MulAut.conj s).toMonoidHom ≠ M) {y : X} (hy2 : y * y = 1)
    (hys : y * s = s * y) (hyM : y ∈ normalizer (M : Set X)) (hyZ : y ∈ normalizer (Z : Set X))
    (hfix : fixCount ((AhatModel.ofCover hM.2).perm y hyM) = n - 4) :
    ∃ B, Sec5Comp X n (centralizer ({s} : Set X)) B ∧
      ∃ b ∈ B, ⁅b, y⁆ ∉ oddCoreOf (centralizer ({s} : Set X)) := by
  classical
  by_contra hcon
  push Not at hcon
  have hn : 8 ≤ n := h.maxdeg.1
  have hy1 : y ≠ 1 := by
    intro e
    subst e
    have h1 : (AhatModel.ofCover hM.2).perm 1 hyM = 1 := (AhatModel.ofCover hM.2).perm_one hn
    rw [h1] at hfix
    have h8 : fixCount (1 : Perm (Fin n)) = n := by unfold fixCount; simp
    omega
  have hy2' : y ^ 2 = 1 := by rw [sq]; exact hy2
  have hyCs : y ∈ centralizer ({s} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hys
  obtain ⟨B, hB, -⟩ := h.exists_comp_centralizer hs
  have hscj : y ∈ centralizerSection B (pPrimeCoreOf 2 B) :=
    normalizes_isPCompIn_of_comm_mem hB.isPCompIn (Subgroup.le_normalizer hyCs)
      (fun l hl => hcon B hB l hl)
  have hJ := K0_ne_bot_of_centralizerSection hy2' hB hscj
  obtain ⟨u, huZ, hu1, hus, huy, hlay⟩ :=
    bcdEight_u_cent h hs hzs hn8 hM hMs hy2 hy1 hys hyM hyZ hfix hJ
  exact bcdEight_contra h hs hy2 hys huZ hu1 hus huy hlay hB hscj

theorem sw2_contra_eight (h : Sec5Data X n z Z S) (hs : IsSec5Inv X Z s) (hzs : z * s = s * z)
    (hn8 : n = 8) {M : Subgroup X} (hM : Sec5Comp X n (centralizer ({z} : Set X)) M)
    (hMs : M.map (MulAut.conj s).toMonoidHom ≠ M) {y : X} (hy2 : y * y = 1)
    (hyz : y * z = z * y) (hys : y * s = s * y) (hyM : y ∈ normalizer (M : Set X))
    (hfix : fixCount ((AhatModel.ofCover hM.2).perm y hyM) = n - 4) :
    ∃ B, Sec5Comp X n (centralizer ({s} : Set X)) B ∧
      ∃ b ∈ B, ⁅b, y⁆ ∉ oddCoreOf (centralizer ({s} : Set X)) := by
  obtain ⟨Z', S', h', hs', hyZ'⟩ := exists_datum_normalized h hs hzs hy2 hyz hys hM hMs
  exact bcdEight_core h' hs' hzs hn8 hM hMs hy2 hys hyM hyZ' hfix

end Eight

end CFSG.OddStandard.Solomon75
