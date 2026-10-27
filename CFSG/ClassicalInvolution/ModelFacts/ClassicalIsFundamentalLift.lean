module

public import CFSG.ClassicalInvolution.Generic.StepQuasisimple
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups commutatorElement

theorem open_isQuasisimple {G : Type*} [Group G] (h : CFSG.IsQuasisimple G) :
    CFSG.Open.IsQuasisimple G :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

theorem isSubnormal_comap {G H : Type*} [Group G] [Group H] (ψ : G →* H) {A B : Subgroup H}
    (h : IsSubnormal A B) : IsSubnormal (A.comap ψ) (B.comap ψ) :=
  h.comap ψ

theorem eq_top_of_central_odd_index {J : Type} [Group J] [Finite J]
    (hO : classicalInvolutionOddCore J = ⊥) {M : Subgroup J} (hM : M ≤ Subgroup.center J)
    (hodd : Odd M.index) : M = ⊤ := by
  have hM2 : IsPGroup 2 M := (isPGroup_center_of_corefree hO).to_le hM
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hM2
  have hcop : (Nat.card M).Coprime M.index := by
    rw [hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  have : M.Normal := Subgroup.normal_of_le_center hM
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hHn : H.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨⟨m, h⟩, hmh⟩ := hH.surjective g
    have hg : g = m * h := hmh.symm
    have hmc : ∀ y : J, (m : J) * y = y * m := fun y =>
      (Subgroup.mem_center_iff.mp (hM m.2) y).symm
    rw [hg]
    have : (m : J) * (h : J) * x * ((m : J) * (h : J))⁻¹ = (h : J) * x * (h : J)⁻¹ := by
      rw [mul_inv_rev]
      calc (m : J) * h * x * ((h : J)⁻¹ * (m : J)⁻¹)
          = m * (h * x * (h : J)⁻¹) * (m : J)⁻¹ := by group
        _ = (h * x * (h : J)⁻¹) * m * (m : J)⁻¹ := by rw [hmc]
        _ = h * x * (h : J)⁻¹ := by group
    rw [this]
    exact H.mul_mem (H.mul_mem h.2 hx) (H.inv_mem h.2)
  have hHcard : Nat.card H = M.index := by
    have h1 := hH.card_mul_card
    have h2 := Subgroup.card_mul_index M
    have hpos : 0 < Nat.card M := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  have hHodd : Odd (Nat.card H) := hHcard ▸ hodd
  have hle : H ≤ classicalInvolutionOddCore J :=
    CFSG.ComponentClassification.OddCore.maximal J H hHn hHodd
  rw [hO, le_bot_iff] at hle
  have : Nat.card H = 1 := by rw [hle]; exact Subgroup.card_bot
  rw [hHcard] at this
  exact Subgroup.index_eq_one.mp this

theorem odd_ker_of_perfect_central_cover {L : Type} [Group L] [Finite L] (hL : Group.IsPerfect L)
    {k : Type} [Field k] [Finite k] (hk : ringChar k ≠ 2)
    (μ : L →* Matrix.SpecialLinearGroup (Fin 2) k) (hμ : Function.Surjective μ)
    {M : Subgroup L} (hMc : M ≤ Subgroup.center L) (hodd : Odd (M.relIndex μ.ker)) : Odd (Nat.card μ.ker) := by
  set J : Subgroup L := μ.ker with hJ
  set O : Subgroup J := classicalInvolutionOddCore J with hO
  set H' : Subgroup L := O.map J.subtype with hH'
  have hH'le : H' ≤ J := Subgroup.map_subtype_le O
  have hH'n : H'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨h, hh, rfl⟩ := hn
    have hc : O.map (MulAut.conjNormal (H := J) g).toMonoidHom = O :=
      CFSG.ComponentClassification.OddCore.char_invariant _
    have hmem : (MulAut.conjNormal (H := J) g) h ∈ O := by
      have := Subgroup.mem_map_of_mem (MulAut.conjNormal (H := J) g).toMonoidHom hh
      rwa [hc] at this
    exact ⟨_, hmem, by simp [MulAut.conjNormal_apply]⟩
  have hOq : classicalInvolutionOddCore (J ⧸ O) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree J
  set Mj : Subgroup J := M.subgroupOf J with hMj
  have hMcJ : Mj ≤ Subgroup.center J := fun x hx => by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hMc (Subgroup.mem_subgroupOf.mp hx)) y)
  have hMhatc : Mj.map (QuotientGroup.mk' O) ≤ Subgroup.center (J ⧸ O) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O q
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hMcJ hx) y]
  have hMhatodd : Odd (Mj.map (QuotientGroup.mk' O)).index := by
    have h1 : (Mj.map (QuotientGroup.mk' O)).index ∣ Mj.index :=
      Subgroup.index_map_dvd Mj (QuotientGroup.mk'_surjective O)
    exact Odd.of_dvd_nat (show Odd Mj.index from hodd) h1
  have htop : Mj.map (QuotientGroup.mk' O) = ⊤ :=
    eq_top_of_central_odd_index hOq hMhatc hMhatodd
  have hmemhat : ∀ j : J, QuotientGroup.mk' O j ∈ Mj.map (QuotientGroup.mk' O) := fun j => by
    rw [htop]
    exact Subgroup.mem_top _
  have hA : ∀ j : J, ∃ m ∈ M, ∃ h ∈ H', (j : L) = m * h := by
    intro j
    obtain ⟨m, hm, hmj⟩ := hmemhat j
    have hmM : (m : L) ∈ M := Subgroup.mem_subgroupOf.mp hm
    have hh : m⁻¹ * j ∈ O := QuotientGroup.eq.mp hmj
    refine ⟨m, hmM, ((m⁻¹ * j : J) : L), ⟨_, hh, rfl⟩, ?_⟩
    simp
  have hB : ∀ j : J, ∃ n : ℕ, (j : L) ^ (2 ^ n) ∈ H' := by
    intro j
    have hc : QuotientGroup.mk' O j ∈ Subgroup.center (J ⧸ O) := hMhatc (hmemhat j)
    obtain ⟨n, hn⟩ := isPGroup_center_of_corefree hOq ⟨_, hc⟩
    refine ⟨n, ?_⟩
    have h1 : (QuotientGroup.mk' O j) ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    rw [← map_pow] at h1
    have h2 : j ^ (2 ^ n) ∈ O := (QuotientGroup.eq_one_iff _).mp h1
    exact ⟨_, h2, by simp⟩
  let η : L ⧸ H' →* Matrix.SpecialLinearGroup (Fin 2) k :=
    QuotientGroup.lift H' μ (fun x hx => hH'le hx)
  have hη : ∀ l : L, η (QuotientGroup.mk l) = μ l := fun l => rfl
  have : Group.IsPerfect (L ⧸ H') := Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' H')
    (QuotientGroup.mk'_surjective H')
  have hηsurj : Function.Surjective η := fun s => by
    obtain ⟨l, rfl⟩ := hμ s
    exact ⟨QuotientGroup.mk l, hη l⟩
  have hηker : ∀ x ∈ η.ker, ∃ j : J, x = QuotientGroup.mk (j : L) := by
    intro x hx
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨⟨l, (hη l).symm.trans hx⟩, rfl⟩
  have hηcen : η.ker ≤ Subgroup.center (L ⧸ H') := by
    intro x hx
    obtain ⟨j, rfl⟩ := hηker x hx
    obtain ⟨m, hmM, h, hh, hjmh⟩ := hA j
    rw [hjmh, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff h).mpr hh, mul_one,
      Subgroup.mem_center_iff]
    intro y
    obtain ⟨l', rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      Subgroup.mem_center_iff.mp (hMc hmM) l']
  have hη2 : IsPGroup 2 η.ker := by
    rintro ⟨x, hx⟩
    obtain ⟨j, rfl⟩ := hηker x hx
    obtain ⟨n, hn⟩ := hB j
    refine ⟨n, Subtype.ext ?_⟩
    show (QuotientGroup.mk (j : L) : L ⧸ H') ^ (2 ^ n) = 1
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hn
  have hsplit : ∀ (E : Type) [Group E] [Finite E]
      (π : E →* Matrix.SpecialLinearGroup (Fin 2) k), Function.Surjective π →
        π.ker ≤ Subgroup.center E → IsPGroup 2 π.ker →
          ∃ σ : Matrix.SpecialLinearGroup (Fin 2) k →* E, ∀ x, π (σ x) = x := by
    intro E _ _ π hπ hcen h2
    obtain ⟨β, hβ⟩ := CFSG.LieType.CentralExt.exists_lift hk hπ hcen h2 (MonoidHom.id _)
    exact ⟨β, fun x => DFunLike.congr_fun hβ x⟩
  obtain ⟨α, -, -, hker⟩ := CFSG.LieType.Steinberg.exists_surjective_of_isPerfect
    (β := MonoidHom.id (Matrix.SpecialLinearGroup (Fin 2) k)) hsplit Function.surjective_id
    hηsurj hηcen hη2
  rw [MonoidHom.ker_id, Subgroup.map_bot] at hker
  have hJH : ∀ j : J, (j : L) ∈ H' := by
    intro j
    have hx : (QuotientGroup.mk (j : L) : L ⧸ H') ∈ η.ker := by
      rw [MonoidHom.mem_ker, hη]
      exact j.2
    rw [hker, Subgroup.mem_bot] at hx
    exact (QuotientGroup.eq_one_iff _).mp hx
  have hOtop : O = ⊤ := by
    rw [eq_top_iff]
    intro j _
    obtain ⟨o, ho, hoj⟩ := hJH j
    have : o = j := Subtype.ext hoj
    exact this ▸ ho
  have hOodd : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card J
  rw [hOtop, Subgroup.card_top] at hOodd
  exact hOodd

section Lift

variable {p f : ℕ} [Fact p.Prime]

theorem IsClassicalMember.exists_lift (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K X : Type} [Group K]
    [Finite K] [Group X] (ψ : K →* X) (hψ : Function.Surjective ψ)
    (hcen : ψ.ker ≤ Subgroup.center K) {L : Subgroup X} {z : X}
    (h : IsClassicalMember p f L z) :
    ∃ (L' : Subgroup K) (z' : K), IsClassicalMember p f L' z' ∧ L'.map ψ = L ∧ ψ z' = z := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have : Finite X := Finite.of_surjective ψ hψ
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have : NeZero f := ⟨hf⟩
  have hk : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp2
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hcard]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h3 : 3 ≤ Nat.card (GaloisField p f) := by
    rw [hcard]
    omega
  set Lpre : Subgroup K := L.comap ψ with hLpre
  set L' : Subgroup K := ⁅Lpre, Lpre⁆ with hL'
  have hLmap : Lpre.map ψ = L := Subgroup.map_comap_eq_self_of_surjective hψ L
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp h.perfect
  have hL'map : L'.map ψ = L := by
    rw [hL', Subgroup.map_commutator, hLmap, hLperf]
  have hL'le : L' ≤ Lpre := Subgroup.commutator_le.mpr fun a ha b hb =>
    Lpre.mul_mem (Lpre.mul_mem (Lpre.mul_mem ha hb) (Lpre.inv_mem ha)) (Lpre.inv_mem hb)
  have hdec : ∀ x ∈ Lpre, ∃ n ∈ ψ.ker, ∃ l ∈ L', x = n * l := by
    intro x hx
    have hx' : ψ x ∈ L'.map ψ := by rw [hL'map]; exact hx
    obtain ⟨l, hl, hlx⟩ := hx'
    refine ⟨x * l⁻¹, ?_, l, hl, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hlx, mul_inv_cancel]
  have hL'perf : ⁅L', L'⁆ = L' := by
    refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb =>
      L'.mul_mem (L'.mul_mem (L'.mul_mem ha hb) (L'.inv_mem ha)) (L'.inv_mem hb)) ?_
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    obtain ⟨n₁, hn₁, l₁, hl₁, rfl⟩ := hdec x hx
    obtain ⟨n₂, hn₂, l₂, hl₂, rfl⟩ := hdec y hy
    rw [CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center (hcen hn₁) (hcen hn₂)]
    exact Subgroup.commutator_mem_commutator hl₁ hl₂
  have : Finite ↥L' := inferInstance
  have hperf'' : Group.IsPerfect ↥L' := Subgroup.isPerfect_iff.mpr hL'perf
  obtain ⟨z₁, hz₁, hz₁ψ⟩ : z ∈ L'.map ψ := by rw [hL'map]; exact h.mem
  have hz2 : z ^ 2 = 1 := by
    rw [← h.orderOf_eq_two]
    exact pow_orderOf_eq_one z
  obtain ⟨e⟩ := h.nonempty_equiv
  let ψ' : ↥L' →* ↥L := (ψ.comp L'.subtype).codRestrict L fun x => by
    have : ψ x.1 ∈ L'.map ψ := Subgroup.mem_map_of_mem ψ x.2
    rwa [hL'map] at this
  have hψ' : Function.Surjective ψ' := by
    rintro ⟨y, hy⟩
    have : y ∈ L'.map ψ := by rw [hL'map]; exact hy
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨⟨x, hx⟩, rfl⟩
  let μ : ↥L' →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p f) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (classicalInvolutionOddCore ↥L)).comp ψ')
  have hμ : Function.Surjective μ :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp hψ')
  have hμker : μ.ker = (classicalInvolutionOddCore ↥L).comap ψ' := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap]
    rw [show μ x = e ((QuotientGroup.mk' (classicalInvolutionOddCore ↥L)) (ψ' x)) from rfl]
    rw [← map_one e, e.injective.eq_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set M : Subgroup ↥L' := ψ'.ker with hM
  have hMψ : ∀ m : ↥L', m ∈ M → ψ m.1 = 1 := fun m hm =>
    congrArg Subtype.val (MonoidHom.mem_ker.mp hm)
  have hMc : M ≤ Subgroup.center ↥L' := by
    intro m hm
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hcen (hMψ m hm)) y.1)
  have hMJ : M ≤ μ.ker := by
    rw [hμker]
    intro m hm
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hm]
    exact Subgroup.one_mem _
  have hodd1 : Odd (M.relIndex μ.ker) := by
    rw [hM, Subgroup.relIndex_ker, hμker, Subgroup.map_comap_eq_self_of_surjective hψ']
    exact CFSG.ComponentClassification.OddCore.odd_card ↥L
  have hJodd : Odd (Nat.card μ.ker) :=
    odd_ker_of_perfect_central_cover hperf'' hk μ hμ hMc hodd1
  have hModd : Odd (Nat.card M) := Odd.of_dvd_nat hJodd (Subgroup.card_dvd_of_le hMJ)
  set m := Nat.card M with hm
  set z' : K := z₁ ^ m with hz'
  have hz'L : z' ∈ L' := L'.pow_mem hz₁ m
  have hψz' : ψ z' = z := by
    rw [hz', map_pow, hz₁ψ]
    obtain ⟨k, hk'⟩ := hModd
    rw [hk', pow_succ, pow_mul, hz2, one_pow, one_mul]
  have hz'2 : z' ^ 2 = 1 := by
    have hmem : (⟨z₁ ^ 2, L'.pow_mem hz₁ 2⟩ : ↥L') ∈ M := by
      rw [hM, MonoidHom.mem_ker]
      apply Subtype.ext
      show ψ (z₁ ^ 2) = 1
      rw [map_pow, hz₁ψ, hz2]
    have h1 : (⟨⟨z₁ ^ 2, L'.pow_mem hz₁ 2⟩, hmem⟩ : M) ^ m = 1 := pow_card_eq_one'
    have h2 := congrArg (fun x : M => ((x : ↥L') : K)) h1
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
    rw [hz', ← pow_mul, mul_comm, pow_mul]
    exact h2
  have hz'ne : z' ≠ 1 := by
    intro h1
    rw [h1, map_one] at hψz'
    exact h.ne_one hψz'.symm
  have hz'ord : orderOf z' = 2 := orderOf_eq_prime hz'2 hz'ne
  have hcomm : ∀ l ∈ L', ⁅l, z'⁆ ∈ Subgroup.center K := by
    intro l hl
    apply hcen
    rw [MonoidHom.mem_ker, map_commutatorElement, hψz']
    have hlL : ψ l ∈ L := by
      have : ψ l ∈ L'.map ψ := Subgroup.mem_map_of_mem ψ hl
      rwa [hL'map] at this
    have hlC : ψ l ∈ Subgroup.centralizer ({z} : Set X) := isSubnormal_le h.subnormal hlL
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hlC)
  have hLC : L' ≤ Subgroup.centralizer ({z'} : Set K) := by
    let φ : ↥L' →* Subgroup.center K :=
      { toFun := fun l => ⟨⁅(l : K), z'⁆, hcomm l l.2⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := by
          intro a b
          apply Subtype.ext
          have hb : ⁅(b : K), z'⁆ ∈ Subgroup.center K := hcomm b b.2
          have key : ⁅(a : K) * b, z'⁆ =
              ((a : K) * ⁅(b : K), z'⁆ * (a : K)⁻¹) * ⁅(a : K), z'⁆ := by
            simp only [commutatorElement_def]
            group
          have hconj : (a : K) * ⁅(b : K), z'⁆ * (a : K)⁻¹ = ⁅(b : K), z'⁆ := by
            rw [Subgroup.mem_center_iff.mp hb (a : K), mul_inv_cancel_right]
          show ⁅(a : K) * b, z'⁆ = ⁅(a : K), z'⁆ * ⁅(b : K), z'⁆
          rw [key, hconj]
          exact (Subgroup.mem_center_iff.mp hb ⁅(a : K), z'⁆).symm }
    have hker : commutator ↥L' ≤ φ.ker := Abelianization.commutator_subset_ker φ
    rw [hperf''.commutator_eq_top] at hker
    intro l hl
    have hφ : φ ⟨l, hl⟩ = 1 := MonoidHom.mem_ker.mp (hker (Subgroup.mem_top _))
    have h1 : ⁅l, z'⁆ = 1 := congrArg Subtype.val hφ
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hsub : IsSubnormal L' (Subgroup.centralizer ({z'} : Set K)) := by
    have h1 := isSubnormal_inf (isSubnormal_comap ψ h.subnormal)
      (Subgroup.centralizer ({z'} : Set K))
    have h2 : (Subgroup.centralizer ({z} : Set X)).comap ψ ⊓
        Subgroup.centralizer ({z'} : Set K) = Subgroup.centralizer ({z'} : Set K) := by
      apply inf_eq_right.mpr
      intro c hc
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, ← hψz', ← map_mul,
        ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hc]
    rw [h2] at h1
    refine isSubnormal_trans (isSubnormal_of_normal_subgroupOf (le_inf hL'le hLC) ?_) h1
    rw [Subgroup.normal_subgroupOf_iff (le_inf hL'le hLC)]
    intro x k hx hk
    obtain ⟨n, hn, l, hl, hkl⟩ := hdec k hk.1
    have : k * x * k⁻¹ = l * x * l⁻¹ := by
      rw [hkl]
      calc n * l * x * (n * l)⁻¹ = n * (l * x * l⁻¹) * n⁻¹ := by group
        _ = l * x * l⁻¹ := CFSG.LieType.Steinberg.mul_mul_inv_of_mem_center (hcen hn) _
    rw [this]
    exact L'.mul_mem (L'.mul_mem hl hx) (L'.inv_mem hl)
  refine ⟨L', z', ⟨hz'ord, hz'L, hperf'', hsub, ?_⟩, hL'map, hψz'⟩
  have hOle : classicalInvolutionOddCore ↥L' ≤ μ.ker := by
    have hnorm : ((classicalInvolutionOddCore ↥L').map μ).Normal :=
      (classicalInvolutionOddCore_normal _).map μ hμ
    have hoddN : Odd (Nat.card ((classicalInvolutionOddCore ↥L').map μ)) :=
      Odd.of_dvd_nat (CFSG.ComponentClassification.OddCore.odd_card ↥L')
        (Subgroup.card_map_dvd _ _)
    exact (Subgroup.map_eq_bot_iff _).mp (sl2_normal_odd hodd h3 _ hnorm hoddN)
  have hJle : μ.ker ≤ classicalInvolutionOddCore ↥L' :=
    CFSG.ComponentClassification.OddCore.maximal ↥L' μ.ker (MonoidHom.normal_ker μ) hJodd
  have hOJ : classicalInvolutionOddCore ↥L' = μ.ker := le_antisymm hOle hJle
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hOJ).trans
    (QuotientGroup.quotientKerEquivOfSurjective μ hμ)⟩

end Lift

end CFSG.ClassicalInvolution.ModelFacts
