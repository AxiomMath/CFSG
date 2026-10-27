module

public import CFSG.ClassicalInvolution.LBalance.Glauberman.SemidirectSetup
public import CFSG.ClassicalInvolution.LBalance.Glauberman.PGroupCommutator
public import CFSG.ClassicalInvolution.LBalance.Glauberman.Lemma1

public section

namespace CFSG.ClassicalInvolution.GlaubermanAut

open SemidirectProduct CFSG.ABGLocalTools

section PartA

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {A : Subgroup (MulAut G)}

theorem mem_normalizer_zpowers_of_commute {Ω : Type*} [Group Ω] {t a : Ω} (h : Commute t a) :
    t ∈ Subgroup.normalizer (Subgroup.zpowers a : Set Ω) := by
  have key : ∀ y ∈ Subgroup.zpowers a, t * y * t⁻¹ = y := by
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [(h.zpow_right i).eq]
    group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [key y hy]
    exact hy
  · intro hy
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hy' : y = a ^ i := by
      calc y = t⁻¹ * (t * y * t⁻¹) * t := by group
        _ = t⁻¹ * a ^ i * t := by rw [hi]
        _ = a ^ i := by rw [(h.inv_left.zpow_right i).eq]; group
    rw [hy']
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) i

omit [Finite G] in
theorem inr_comm_of_right_central {hA : ∀ α ∈ A, ∀ s ∈ S, α s = s} {q : AutExt A} (hq : q.left ∈ S)
    (a : A) (h : a * q.right = q.right * a) : (inr a : AutExt A) * q = q * inr a := by
  conv_lhs => rw [inl_inr_decomp q]
  conv_rhs => rw [inl_inr_decomp q]
  rw [← mul_assoc, inr_comm_inl (hA := hA) a hq, mul_assoc, mul_assoc, ← map_mul, ← map_mul, h]

theorem isMulCommutative_of_isPGroup_two
    (hG : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hSp : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) (hA : ∀ α ∈ A, ∀ s ∈ S, α s = s)
    (hAp : IsPGroup 2 A) (α β : A) : α * β = β * α := by
  by_contra hcon
  obtain ⟨α, β, hτ1, hτ2, hτc⟩ := exists_central_involution_commutator hAp ⟨α, β, hcon⟩
  set τ : A := α⁻¹ * β⁻¹ * α * β with hτ
  have hBp : IsPGroup 2 (⊤ : Subgroup A) :=
    hAp.of_injective (⊤ : Subgroup A).subtype (Subgroup.subtype_injective _)
  obtain ⟨g, hgH, hgT, hgN⟩ :=
    exists_conj_not_normalizer hG hSp hSi hA hBp (Subgroup.mem_top τ) hτ1 hτ2
  set H := hSub A ⊤ with hH
  set T := tSub S A hA ⊤ with hT
  set τ' : AutExt A := inr τ with hτ'
  set P := Subgroup.zpowers τ' with hP
  have hTH : IsSylowOf 2 T H := isSylowOf_tSub hSp hSi hBp
  have hτ'T : τ' ∈ T := ⟨by simp [hτ'], Subgroup.mem_top _⟩
  have hτ'c : ∀ t ∈ T, t * τ' = τ' * t := fun t ht =>
    (inr_comm_of_right_central (hA := hA) ht.1 τ (hτc t.right)).symm
  have hPT : T ≤ Subgroup.normalizer (P : Set (AutExt A)) := fun t ht =>
    mem_normalizer_zpowers_of_commute (hτ'c t ht)
  have hPleT : P ≤ T := Subgroup.zpowers_le.2 hτ'T
  obtain ⟨Q, ⟨hPQ, hQT, hb, hc, h, hhmem, ⟨r, hr, hr2, n, hord⟩, hhP⟩, hgen⟩ :=
    lemma1_generated hTH hPT hPleT hgH hgT hgN
  have hhr : rightHom h = 1 := by
    have h1 : orderOf (rightHom h) ∣ orderOf h := orderOf_map_dvd rightHom h
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hAp (rightHom h)
    rw [hk, hord] at h1
    have hcop : Nat.Coprime (2 ^ k) (r ^ n) :=
      Nat.Coprime.pow k n ((Nat.coprime_primes Nat.prime_two hr).2 hr2.symm)
    have h2 : 2 ^ k = 1 := Nat.Coprime.eq_one_of_dvd hcop h1
    rw [h2] at hk
    exact orderOf_eq_one_iff.1 hk
  have hzn : (Subgroup.zpowers τ).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : Commute g τ := (hτc g).symm
    rw [(hc.zpow_right i).eq]
    simp
  set M : Subgroup (AutExt A) := (Subgroup.zpowers τ).comap rightHom with hM
  have hMn : M.Normal := hzn.comap rightHom
  have hτ'M : τ' ∈ M := by
    show rightHom τ' ∈ Subgroup.zpowers τ
    rw [hτ', rightHom_inr]
    exact Subgroup.mem_zpowers τ
  have hPM : P ≤ M := Subgroup.zpowers_le.2 hτ'M
  have hQM : Q ≤ M := by
    calc Q = Subgroup.closure (genSet H P Q) := hgen
      _ ≤ M := by
        rw [Subgroup.closure_le]
        rintro x ⟨k, -, hkx⟩
        have := hMn.conj_mem _ (hPM hkx) k⁻¹
        have e : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
        rwa [e] at this
  have hτc' : ∀ γ : A, Commute γ τ := fun γ => (hτc γ).symm
  have hQc : ∀ (a : A), ∀ q ∈ Q, (inr a : AutExt A) * q = q * inr a := by
    intro a q hq
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hQM hq)
    refine inr_comm_of_right_central (hA := hA) (hQT hq).1 a ?_
    have hqr : q.right = τ ^ i := hi.symm
    rw [hqr]
    exact (Commute.zpow_right (show Commute a τ from (hτc a).symm) i).eq
  set W : Subgroup (AutExt A) := T ⊓ Subgroup.centralizer (Q : Set (AutExt A)) with hW
  set Gk : Subgroup (AutExt A) := (rightHom : AutExt A →* A).ker with hGk
  set Wk : Subgroup (AutExt A) := W ⊓ Gk with hWk
  set V : Subgroup (AutExt A) := W ⊓ Subgroup.centralizer (Wk : Set (AutExt A)) with hV
  have hmemW : ∀ a : A, (inr a : AutExt A) ∈ W := fun a =>
    ⟨⟨by rw [left_inr]; exact S.one_mem, Subgroup.mem_top _⟩,
      Subgroup.mem_centralizer_iff.2 fun q hq => (hQc a q hq).symm⟩
  have hmemV : ∀ a : A, (inr a : AutExt A) ∈ V := fun a =>
    ⟨hmemW a, Subgroup.mem_centralizer_iff.2 fun y hy => by
      have hyr : y.right = 1 := hy.2
      exact (inr_comm_of_right_central (hA := hA) hy.1.1.1 a
        (by rw [hyr, mul_one, one_mul])).symm⟩
  have hGkn : Gk.Normal := MonoidHom.normal_ker _
  have hhGk : h ∈ Gk := hhr
  have hhW : h ∈ Subgroup.normalizer (W : Set (AutExt A)) := hhmem.2
  have hhWk : h ∈ Subgroup.normalizer (Wk : Set (AutExt A)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyW, hyG⟩
      exact ⟨(Subgroup.mem_normalizer_iff.1 hhW y).1 hyW, hGkn.conj_mem y hyG h⟩
    · rintro ⟨hyW, hyG⟩
      refine ⟨(Subgroup.mem_normalizer_iff.1 hhW y).2 hyW, ?_⟩
      have := hGkn.conj_mem _ hyG h⁻¹
      simpa [mul_assoc] using this
  have hhV : h ∈ Subgroup.normalizer (V : Set (AutExt A)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · rintro ⟨hvW, hvC⟩
      exact ⟨(Subgroup.mem_normalizer_iff.1 hhW v).1 hvW,
        conj_mem_centralizer_of_mem_normalizer hhWk hvC⟩
    · rintro ⟨hvW, hvC⟩
      refine ⟨(Subgroup.mem_normalizer_iff.1 hhW v).2 hvW, ?_⟩
      have := conj_mem_centralizer_of_mem_normalizer (inv_mem hhWk) hvC
      simpa [mul_assoc] using this
  have hx : ∀ a : A, (inr a : AutExt A)⁻¹ * h⁻¹ * inr a * h ∈ V ∧
      (inr a : AutExt A)⁻¹ * h⁻¹ * inr a * h ∈ Gk := by
    intro a
    constructor
    · have h1 : (inr a : AutExt A) ∈ V := hmemV a
      have h2 : h⁻¹ * inr a * h ∈ V := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hhV) (inr a)).1 h1
        simpa using this
      have := V.mul_mem (V.inv_mem h1) h2
      simpa [mul_assoc] using this
    · have hhr' : h.right = 1 := hhr
      show rightHom _ = 1
      simp [hhr']
  have hxc : ∀ a : A, ∀ v ∈ V, ((inr a : AutExt A)⁻¹ * h⁻¹ * inr a * h) * v =
      v * ((inr a : AutExt A)⁻¹ * h⁻¹ * inr a * h) := fun a v hv =>
    Subgroup.mem_centralizer_iff.1 hv.2 _ ⟨(hx a).1.1, (hx a).2⟩
  have hτ'eq : τ' = (inr α : AutExt A)⁻¹ * (inr β)⁻¹ * inr α * inr β := by
    rw [hτ', hτ]
    simp [map_mul, map_inv]
  have key : h⁻¹ * τ' * h = τ' := by
    have hA1 : h⁻¹ * (inr α : AutExt A) * h =
        inr α * ((inr α : AutExt A)⁻¹ * h⁻¹ * inr α * h) := by group
    have hB1 : h⁻¹ * (inr β : AutExt A) * h =
        inr β * ((inr β : AutExt A)⁻¹ * h⁻¹ * inr β * h) := by group
    calc h⁻¹ * τ' * h
        = (h⁻¹ * inr α * h)⁻¹ * (h⁻¹ * inr β * h)⁻¹ * (h⁻¹ * inr α * h) * (h⁻¹ * inr β * h) := by
          rw [hτ'eq]
          group
      _ = (inr α * ((inr α : AutExt A)⁻¹ * h⁻¹ * inr α * h))⁻¹ *
            (inr β * ((inr β : AutExt A)⁻¹ * h⁻¹ * inr β * h))⁻¹ *
            (inr α * ((inr α : AutExt A)⁻¹ * h⁻¹ * inr α * h)) *
            (inr β * ((inr β : AutExt A)⁻¹ * h⁻¹ * inr β * h)) := by rw [hA1, hB1]
      _ = (inr α : AutExt A)⁻¹ * (inr β)⁻¹ * inr α * inr β :=
          commutator_mul_central _ _ _ _ (hxc α _ (hmemV α)) (hxc α _ (hmemV β))
            (hxc α _ (hx β).1) (hxc β _ (hmemV α)) (hxc β _ (hmemV β))
      _ = τ' := hτ'eq.symm
  apply hhP
  apply mem_normalizer_zpowers_of_commute
  calc h * τ' = h * (h⁻¹ * τ' * h) := by rw [key]
    _ = τ' * h := by group

end PartA

end CFSG.ClassicalInvolution.GlaubermanAut
