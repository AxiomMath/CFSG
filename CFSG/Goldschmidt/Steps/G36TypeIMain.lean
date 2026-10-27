module

public import CFSG.Goldschmidt.Steps.G36Sz8
public import CFSG.Goldschmidt.Steps.G36TypeII
import CFSG.Walter.PSL2Facts.Even
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.ComponentClassification
open scoped MatrixGroups

variable {L : Type} [Group L] [Finite L] {A₀ : Subgroup L} {T₀ : Sylow 2 L}

omit [Finite L] in
theorem commutator_mem_center_of_map_eq
    (hmap : A₀.map (QuotientGroup.mk' (Subgroup.center L)) =
      (T₀ : Subgroup L).map (QuotientGroup.mk' (Subgroup.center L)) ⊓
        Subgroup.centralizer (((T₀ : Subgroup L).map
          (QuotientGroup.mk' (Subgroup.center L)) : Subgroup _) : Set (L ⧸ Subgroup.center L)))
    {a x : L} (ha : a ∈ A₀) (hx : x ∈ (T₀ : Subgroup L)) :
    a * x * a⁻¹ * x⁻¹ ∈ Subgroup.center L := by
  have hab : (a : L ⧸ Subgroup.center L) ∈ A₀.map (QuotientGroup.mk' (Subgroup.center L)) :=
    ⟨a, ha, rfl⟩
  rw [hmap] at hab
  have hc := Subgroup.mem_centralizer_iff.mp hab.2 (x : L ⧸ Subgroup.center L) ⟨x, hx, rfl⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, ← hc]
  group

theorem commute_of_newPair (hNP : S_GNewPair) (h : G36Hyp L A₀ T₀)
    (hmap : A₀.map (QuotientGroup.mk' (Subgroup.center L)) =
      (T₀ : Subgroup L).map (QuotientGroup.mk' (Subgroup.center L)) ⊓
        Subgroup.centralizer (((T₀ : Subgroup L).map
          (QuotientGroup.mk' (Subgroup.center L)) : Subgroup _) : Set (L ⧸ Subgroup.center L)))
    (htype : (∃ n : ℕ, 2 ≤ n ∧ Nonempty (L ⧸ Subgroup.center L ≃* Sz n)) ∨
      (∃ f : ℕ, 2 ≤ f ∧ Nonempty (L ⧸ Subgroup.center L ≃* PSU3 2 f)))
    (hZ2 : ∃ z ∈ Subgroup.center L, z ≠ 1 ∧ ∃ k : ℕ, z ^ 2 ^ k = 1) :
    ∀ t ∈ (T₀ : Subgroup L), ∀ a ∈ A₀, t * a = a * t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Subgroup.center L with hZdef
  set O := goldschmidtOddCore L with hOdef
  have hOodd : Odd (Nat.card O) := by
    have := CFSG.pPrimeCore_coprime_card (p := 2) (G := L)
    rw [hOdef, goldschmidtOddCore_eq_pPrimeCore]
    exact Nat.coprime_two_left.mp this
  have hOZ : O ≤ Z := by
    rcases Quasisimple.normal_le_center_or_eq_top h.quasisimple O with hle | htop
    · exact hle
    · exfalso
      apply h.not_le_center
      intro a ha
      have ha1 : a = 1 := eq_one_of_pow_two_pow_eq_one hOodd (htop ▸ Subgroup.mem_top a)
        (k := 1) (by rw [pow_one]; exact h.sq_eq_one ha)
      rw [ha1]
      exact Z.one_mem
  set ψ := QuotientGroup.mk' O with hψdef
  have hψs : Function.Surjective ψ := QuotientGroup.mk'_surjective O
  have hQ : CFSG.Open.IsQuasisimple (L ⧸ O) := Quasisimple.central_quotient h.quasisimple O hOZ
  have : Group.IsPerfect L := ⟨h.quasisimple.1⟩
  have hker : ψ.ker ≤ Z := by rw [QuotientGroup.ker_mk']; exact hOZ
  have hZQ : (Subgroup.center (L ⧸ O)).comap ψ = Z :=
    Quasisimple.center_comap_of_central_kernel ψ hψs hker
  have hZQ' : Z.map ψ = Subgroup.center (L ⧸ O) :=
    Quasisimple.center_map_of_central_kernel ψ hψs hker
  have hmemZQ : ∀ w : L, ψ w ∈ Subgroup.center (L ⧸ O) ↔ w ∈ Z := fun w => by
    rw [← hZQ, Subgroup.mem_comap]
  let eQ : (L ⧸ O) ⧸ Subgroup.center (L ⧸ O) ≃* L ⧸ Z :=
    (QuotientGroup.congr (Z.map ψ) (Subgroup.center (L ⧸ O)) (MulEquiv.refl _)
      (by simpa using hZQ')).symm.trans (QuotientGroup.quotientQuotientEquivQuotient O Z hOZ)
  have hZQ2 : IsPGroup 2 (Subgroup.center (L ⧸ O)) := by
    rintro ⟨g, hg⟩
    rw [← hZQ'] at hg
    obtain ⟨z, hz, rfl⟩ := hg
    refine ⟨(orderOf z).factorization 2, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← map_pow, hψdef, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    have hodd : Odd (orderOf (z ^ 2 ^ (orderOf z).factorization 2)) := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (Nat.ordProj_dvd _ _)]
      exact Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two (orderOf_pos z).ne')
    have hnormal : (Subgroup.zpowers (z ^ 2 ^ (orderOf z).factorization 2)).Normal :=
      Subgroup.normal_of_le_center ((Subgroup.zpowers_le).mpr (Subgroup.pow_mem _ hz _))
    have hle : Subgroup.zpowers (z ^ 2 ^ (orderOf z).factorization 2) ≤ O :=
      le_sSup ⟨hnormal, by rw [Nat.card_zpowers]; exact hodd⟩
    exact hle (Subgroup.mem_zpowers _)
  have hZQne : Subgroup.center (L ⧸ O) ≠ ⊥ := by
    obtain ⟨z, hz, hz1, k, hk⟩ := hZ2
    intro hbot
    have hzQ : ψ z ∈ Subgroup.center (L ⧸ O) := (hmemZQ z).mpr hz
    rw [hbot, Subgroup.mem_bot, hψdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hzQ
    exact hz1 (eq_one_of_pow_two_pow_eq_one hOodd hzQ hk)
  set TQ : Sylow 2 (L ⧸ O) := T₀.mapSurjective hψs with hTQdef
  have hTQ : (TQ : Subgroup (L ⧸ O)) = (T₀ : Subgroup L).map ψ := Sylow.coe_mapSurjective _ _
  have hcommQ : ∀ w : L, ψ w = 1 → w ∈ (T₀ : Subgroup L) → w = 1 := by
    intro w hw hwT
    rw [hψdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hw
    obtain ⟨k, hk⟩ := h.exists_pow_eq_one hwT
    exact eq_one_of_pow_two_pow_eq_one hOodd hw hk
  have hkey : ∀ t ∈ (T₀ : Subgroup L), (∀ x ∈ (T₀ : Subgroup L), t * x * t⁻¹ * x⁻¹ ∈ Z) →
      t ∈ A₀ := by
    intro t ht hcomm
    apply h.mem_of_mk_mem ht
    rw [hmap]
    refine ⟨⟨t, ht, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have h1 : ((t * x * t⁻¹ * x⁻¹ : L) : L ⧸ Z) = 1 := (QuotientGroup.eq_one_iff _).mpr (hcomm x hx)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h1
    change (x : L ⧸ Z) * (t : L ⧸ Z) = (t : L ⧸ Z) * (x : L ⧸ Z)
    calc (x : L ⧸ Z) * (t : L ⧸ Z) =
        ((t : L ⧸ Z) * (x : L ⧸ Z) * (t : L ⧸ Z)⁻¹ * (x : L ⧸ Z)⁻¹)⁻¹ *
          ((t : L ⧸ Z) * (x : L ⧸ Z)) := by group
      _ = (t : L ⧸ Z) * (x : L ⧸ Z) := by rw [h1, inv_one, one_mul]
  have hab : ∀ b ∈ (TQ : Subgroup (L ⧸ O)), ∀ c ∈ (TQ : Subgroup (L ⧸ O)),
      (∀ x ∈ (TQ : Subgroup (L ⧸ O)), b * x * b⁻¹ * x⁻¹ ∈ Subgroup.center (L ⧸ O)) →
      (∀ x ∈ (TQ : Subgroup (L ⧸ O)), c * x * c⁻¹ * x⁻¹ ∈ Subgroup.center (L ⧸ O)) →
      b * c = c * b := by
    intro b hb c hc hbc hcc
    rw [hTQ] at hb hc
    obtain ⟨t, ht, rfl⟩ := hb
    obtain ⟨s, hs, rfl⟩ := hc
    have hA : ∀ u ∈ (T₀ : Subgroup L),
        (∀ x ∈ (TQ : Subgroup (L ⧸ O)), ψ u * x * (ψ u)⁻¹ * x⁻¹ ∈ Subgroup.center (L ⧸ O)) →
        u ∈ A₀ := by
      intro u hu hux
      refine hkey u hu fun x hx => (hmemZQ _).mp ?_
      have := hux (ψ x) (hTQ ▸ ⟨x, hx, rfl⟩)
      rwa [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at this
    rw [← map_mul, ← map_mul, h.mul_comm (hA t ht hbc) (hA s hs hcc)]
  have htypeQ : (∃ n : ℕ, 2 ≤ n ∧ Nonempty ((L ⧸ O) ⧸ Subgroup.center (L ⧸ O) ≃* Sz n)) ∨
      (∃ f : ℕ, 2 ≤ f ∧ Nonempty ((L ⧸ O) ⧸ Subgroup.center (L ⧸ O) ≃* PSU3 2 f)) := by
    rcases htype with ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩
    · exact Or.inl ⟨n, hn, ⟨eQ.trans e⟩⟩
    · exact Or.inr ⟨f, hf, ⟨eQ.trans e⟩⟩
  have hNPQ := hNP (L ⧸ O) hQ hZQ2 hZQne htypeQ TQ hab
  intro t ht a ha
  have hcomm : ψ t * ψ a = ψ a * ψ t := by
    refine hNPQ (ψ a) (hTQ ▸ ⟨a, h.le ha, rfl⟩) ?_ (ψ t) (hTQ ▸ ⟨t, ht, rfl⟩)
    intro x hx
    rw [hTQ] at hx
    obtain ⟨x, hx, rfl⟩ := hx
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hmemZQ]
    exact commutator_mem_center_of_map_eq hmap ha hx
  have h1 : ψ ((a * t)⁻¹ * (t * a)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, hcomm, inv_mul_cancel]
  have h2 := hcommQ _ h1 ((T₀ : Subgroup L).mul_mem
    ((T₀ : Subgroup L).inv_mem ((T₀ : Subgroup L).mul_mem (h.le ha) ht))
    ((T₀ : Subgroup L).mul_mem ht (h.le ha)))
  rw [inv_mul_eq_one] at h2
  exact h2.symm

theorem isMulCommutative_map_of_psl2 {n : ℕ} (hn : 2 ≤ n)
    (e : L ⧸ Subgroup.center L ≃* PSL(2, GaloisField 2 n)) :
    IsMulCommutative ((T₀ : Subgroup L).map (QuotientGroup.mk' (Subgroup.center L))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Tb' : Sylow 2 (L ⧸ Subgroup.center L) :=
    T₀.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center L)) with hTb'
  have hTbcoe : (Tb' : Subgroup (L ⧸ Subgroup.center L)) =
      (T₀ : Subgroup L).map (QuotientGroup.mk' (Subgroup.center L)) :=
    Sylow.coe_mapSurjective _ _
  set S' : Sylow 2 _ := Tb'.mapSurjective (f := e.toMonoidHom) e.surjective with hS'
  have hS'coe : (S' : Subgroup _) =
      (Tb' : Subgroup (L ⧸ Subgroup.center L)).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  rw [hTbcoe] at hS'coe
  obtain ⟨hel, -⟩ := CFSG.Walter.psl2_even_sylow_two hn S'
  refine ⟨⟨fun a b => Subtype.ext (e.injective ?_)⟩⟩
  have hc := hel.toIsMulCommutative.is_comm.comm
    (⟨e a, by rw [hS'coe]; exact ⟨a, a.2, rfl⟩⟩ : (S' : Subgroup _))
    ⟨e b, by rw [hS'coe]; exact ⟨b, b.2, rfl⟩⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
  exact congrArg Subtype.val hc

theorem typeI_dichotomy (hNP : S_GNewPair) (h : G36Hyp L A₀ T₀) (hI : IsGoldTypeI L)
    {Tb D : Subgroup (L ⧸ Subgroup.center L)} {y : L} (hB : G36Borel L A₀ T₀ Tb D y)
    (hnc : ¬ ∀ t ∈ (T₀ : Subgroup L), ∀ a ∈ A₀, t * a = a * t) :
    Nonempty (L ⧸ Subgroup.center L ≃* Sz 1) ∧ Even (Nat.card (Subgroup.center L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap : A₀.map (QuotientGroup.mk' (Subgroup.center L)) =
      (T₀ : Subgroup L).map (QuotientGroup.mk' (Subgroup.center L)) ⊓
        Subgroup.centralizer (((T₀ : Subgroup L).map
          (QuotientGroup.mk' (Subgroup.center L)) : Subgroup _) : Set (L ⧸ Subgroup.center L)) := by
    rw [hB.map_eq, hB.tb_eq]
  have hZ2 : ∃ z ∈ Subgroup.center L, z ≠ 1 ∧ ∃ k : ℕ, z ^ 2 ^ k = 1 := by
    by_contra hcon
    push Not at hcon
    apply hnc
    intro t ht a ha
    have h1 := commutator_mem_center_of_map_eq hmap ha ht
    have h2 : a * t * a⁻¹ * t⁻¹ ∈ (T₀ : Subgroup L) :=
      (T₀ : Subgroup L).mul_mem ((T₀ : Subgroup L).mul_mem ((T₀ : Subgroup L).mul_mem (h.le ha) ht)
        ((T₀ : Subgroup L).inv_mem (h.le ha))) ((T₀ : Subgroup L).inv_mem ht)
    obtain ⟨k, hk⟩ := h.exists_pow_eq_one h2
    by_contra hta
    have hne : a * t * a⁻¹ * t⁻¹ ≠ 1 := by
      intro h3
      apply hta
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
      exact h3.symm
    exact hcon _ h1 hne k hk
  have hev : Even (Nat.card (Subgroup.center L)) := by
    obtain ⟨z, hz, hz1, k, hk⟩ := hZ2
    have hdvd : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨m, -, hzm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hzm
      exact hz1 hzm
    have h2 : 2 ∣ orderOf z := by
      rw [hzm]
      exact dvd_pow_self 2 hm0
    exact even_iff_two_dvd.mpr (h2.trans (Subgroup.orderOf_dvd_natCard _ hz))
  refine ⟨?_, hev⟩
  rcases hI with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exfalso
    apply hnc
    have hab := isMulCommutative_map_of_psl2 (T₀ := T₀) (by omega) e
    have hTA : ∀ t ∈ (T₀ : Subgroup L), t ∈ A₀ := by
      intro t ht
      apply h.mem_of_mk_mem ht
      rw [hmap]
      refine ⟨⟨t, ht, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
      exact congrArg Subtype.val (hab.is_comm.comm ⟨s, hs⟩ ⟨_, ⟨t, ht, rfl⟩⟩)
    intro t ht a ha
    exact h.mul_comm (hTA t ht) ha
  · rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have hn1 : n = 1 := by omega
      subst hn1
      exact ⟨e⟩
    · exact absurd (commute_of_newPair hNP h hmap (Or.inl ⟨n, hn2, ⟨e⟩⟩) hZ2) hnc
  · exact absurd (commute_of_newPair hNP h hmap (Or.inr ⟨n, hn, ⟨e⟩⟩) hZ2) hnc

theorem g36Local_of_typeI (h32 : S_G32) (hNP : S_GNewPair) (h : G36Hyp L A₀ T₀)
    (hI : IsGoldTypeI L) : G36Local L A₀ := by
  obtain ⟨D, y, hB⟩ := exists_g36Borel h32 h hI
  by_cases hc : ∀ t ∈ (T₀ : Subgroup L), ∀ a ∈ A₀, t * a = a * t
  · exact hB.g36Local_of_commute h hc
  · obtain ⟨hsz, hev⟩ := typeI_dichotomy hNP h hI hB hc
    exact hB.g36Local_sz8 h hsz hev hc

theorem g36Local (h32 : S_G32) (hNP : S_GNewPair) (h : G36Hyp L A₀ T₀)
    (hL : IsGoldTypeI L ∨ IsGoldTypeII L) : G36Local L A₀ :=
  hL.elim (g36Local_of_typeI h32 hNP h) (g36Local_of_typeII h)

end CFSG.Goldschmidt
