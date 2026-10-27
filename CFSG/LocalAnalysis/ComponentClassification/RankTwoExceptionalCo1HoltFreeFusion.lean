module

public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDefs

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.HoltFree

open Subgroup CFSG.ABGLocalTools
open CFSG.ComponentClassification.RankTwoSporadic (IsActionHom)

structure Co1TwoCSetting {X : Type} [Group X] [Finite X] (L : Subgroup X)
    (ψ : normalizer (L : Set X) →* Blueprint.NativeSporadic.Co1) (z : X) : Prop where
  act : IsActionHom L ⊤ ψ
  oddCent : Odd (Nat.card (centralizer (L : Set X)))
  mem : z ∈ L
  order : orderOf z = 2
  central : ¬ 2 ∣ (centralizer ({ψ ⟨z, le_normalizer mem⟩} :
    Set Blueprint.NativeSporadic.Co1)).index
  unique : ∀ g : X, g * z * g⁻¹ ∈ L → g ∈ normalizer (L : Set X)

namespace Co1TwoCSetting

variable {X : Type} [Group X] [Finite X] {L : Subgroup X}
  {ψ : normalizer (L : Set X) →* Blueprint.NativeSporadic.Co1} {z : X}
  (h : Co1TwoCSetting L ψ z)
include h

theorem exists_mul {n : X} (hn : n ∈ normalizer (L : Set X)) :
    ∃ a ∈ L, ∃ k ∈ centralizer (L : Set X), n = a * k := by
  obtain ⟨a, ha, hψ⟩ := h.act.exists_eq (ψ ⟨n, hn⟩) (mem_top _)
  have h1 : ψ (⟨a, le_normalizer ha⟩⁻¹ * ⟨n, hn⟩) = 1 := by
    rw [map_mul, map_inv, hψ, inv_mul_cancel]
  exact ⟨a, ha, a⁻¹ * n, (h.act.eq_one_iff _).mp h1, by group⟩

theorem mem_of_pow_mem {k : X} (hk : k ∈ centralizer (L : Set X)) {m : ℕ}
    (hkm : k ^ 2 ^ m ∈ L) : k ∈ L := by
  have hodd : Odd (orderOf k) := h.oddCent.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hk)
  have hcop : Nat.Coprime (2 ^ m) (orderOf k) :=
    Nat.Coprime.pow_left m (Nat.prime_two.coprime_iff_not_dvd.mpr fun h2 =>
      (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2))
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hj]
  exact pow_mem hkm j

theorem le_of_isPGroup {P : Subgroup X} (hP : P ≤ normalizer (L : Set X))
    (h2 : IsPGroup 2 P) : P ≤ L := by
  intro p hp
  obtain ⟨a, ha, k, hk, rfl⟩ := h.exists_mul (hP hp)
  obtain ⟨m, hm⟩ := h2 ⟨_, hp⟩
  have hm' : (a * k) ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hak : Commute a k := mem_centralizer_iff.mp hk a ha
  rw [hak.mul_pow] at hm'
  have hkm : k ^ 2 ^ m ∈ L := by
    rw [eq_inv_of_mul_eq_one_right hm']
    exact inv_mem (pow_mem ha _)
  exact mul_mem ha (h.mem_of_pow_mem hk hkm)

theorem centralizer_conj_le {g : X} (hg : g * z * g⁻¹ ∈ L) :
    centralizer ({g * z * g⁻¹} : Set X) ≤ normalizer (L : Set X) := by
  intro c hc
  have hcg : c * g * z * (c * g)⁻¹ ∈ L := by
    rw [show c * g * z * (c * g)⁻¹ = c * (g * z * g⁻¹) * c⁻¹ by group,
      mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
    exact hg
  rw [show c = c * g * g⁻¹ by group]
  exact mul_mem (h.unique _ hcg) (inv_mem (h.unique _ hg))

theorem normalizer_le_of_conj_mem {T : Subgroup X} (hT : T ≤ L) {g : X}
    (hg : g * z * g⁻¹ ∈ T) : normalizer (T : Set X) ≤ normalizer (L : Set X) := by
  intro n hn
  have h1 : n * (g * z * g⁻¹) * n⁻¹ ∈ T := (mem_normalizer_iff.mp hn _).mp hg
  have h2 : n * g * z * (n * g)⁻¹ ∈ L := by
    rw [show n * g * z * (n * g)⁻¹ = n * (g * z * g⁻¹) * n⁻¹ by group]
    exact hT h1
  rw [show n = n * g * g⁻¹ by group]
  exact mul_mem (h.unique _ h2) (inv_mem (h.unique _ (hT hg)))

theorem comap_centralizer :
    (centralizer ({ψ ⟨z, le_normalizer h.mem⟩} : Set Blueprint.NativeSporadic.Co1)).comap ψ =
      (centralizer ({z} : Set X)).subgroupOf (normalizer (L : Set X)) := by
  ext n
  rw [mem_comap, mem_subgroupOf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hn
    have h1 : ψ (n * ⟨z, le_normalizer h.mem⟩ * n⁻¹ * ⟨z, le_normalizer h.mem⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hn]
      group
    have h2 := (h.act.eq_one_iff _).mp h1
    set c := (n : X) * z * (n : X)⁻¹ * z⁻¹ with hc
    have hcC : c ∈ centralizer (L : Set X) := h2
    have hcL : c ∈ L :=
      mul_mem ((mem_normalizer_iff.mp n.2 z).mp h.mem) (inv_mem h.mem)
    have hz2 : z * z = 1 := by rw [← pow_two, ← h.order, pow_orderOf_eq_one]
    have hcz : z * c = c * z := mem_centralizer_iff.mp hcC z h.mem
    have hcc : c * c = 1 := by
      have e1 : (n : X) * z * (n : X)⁻¹ = c * z := by rw [hc]; group
      have e2 : c * z * (c * z) = 1 := by
        rw [← e1, show (n : X) * z * (n : X)⁻¹ * ((n : X) * z * (n : X)⁻¹) =
          (n : X) * (z * z) * (n : X)⁻¹ by group, hz2, mul_one, mul_inv_cancel]
      calc c * c = c * z * (c * z) * (z * z)⁻¹ := by
            rw [show c * z * (c * z) = c * (z * c) * z by group, hcz]
            group
        _ = 1 := by rw [e2, hz2, inv_one, mul_one]
    have hc1 : c = 1 := by
      have hodd : Odd (orderOf c) := h.oddCent.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hcC)
      have h3 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hcc)
      rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h4 | h4
      · exact orderOf_eq_one_iff.mp h4
      · rw [h4] at hodd
        exact absurd hodd (by decide)
    calc (n : X) * z = (n : X) * z * (n : X)⁻¹ * z⁻¹ * (z * n) := by group
      _ = z * n := by rw [← hc, hc1, one_mul]
  · intro hn
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext hn)

theorem isSylowOf_normalizer {T : Subgroup X}
    (hT : IsSylowOf 2 T (normalizer (L : Set X) ⊓ centralizer ({z} : Set X))) :
    IsSylowOf 2 T (normalizer (L : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : Function.Surjective ψ := fun w => by
    obtain ⟨a, ha, hw⟩ := h.act.exists_eq w (mem_top w)
    exact ⟨_, hw⟩
  have hidx : ¬ 2 ∣ (centralizer ({z} : Set X)).relIndex (normalizer (L : Set X)) := by
    rw [relIndex, ← h.comap_centralizer, index_comap_of_surjective _ hsurj]
    exact h.central
  rw [isSylowOf_iff] at hT ⊢
  obtain ⟨hTle, hT2, hTidx⟩ := hT
  refine ⟨hTle.trans inf_le_left, hT2, fun h2 => ?_⟩
  rw [← relIndex_mul_relIndex T _ _ hTle inf_le_left, inf_relIndex_left] at h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h3 | h3
  · exact hTidx h3
  · exact hidx h3

theorem exists_sylow {P : Subgroup X} (hPL : P ≤ L) (hP : IsPGroup 2 P) :
    ∃ S : Sylow 2 X, P ≤ S ∧ (S : Subgroup X) ≤ L ∧ ∃ g : X, g * z * g⁻¹ ∈ (S : Subgroup X) ∧
      ∀ s ∈ (S : Subgroup X), s * (g * z * g⁻¹) = g * z * g⁻¹ * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (L : Set X) with hN
  have hLN : L ≤ N := le_normalizer
  obtain ⟨T₀, hT₀⟩ := exists_isSylowOf 2 (N ⊓ centralizer ({z} : Set X))
  have hT₀N := h.isSylowOf_normalizer hT₀
  have hT₀z : T₀ ≤ centralizer ({z} : Set X) := hT₀.le.trans inf_le_right
  have hzT₀ : z ∈ T₀ := by
    have hzN : zpowers z ≤ normalizer (T₀ : Set X) := zpowers_le.mpr
      (centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun t ht =>
        mem_centralizer_singleton_iff.mp (hT₀z ht)))
    have hz2 : IsPGroup 2 (zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.order, pow_one])
    have heq := hT₀N.eq_of_le le_sup_left
      (sup_le hT₀N.le (zpowers_le.mpr (hLN h.mem)))
      (IsPGroup.to_sup_of_normal_left' hT₀N.isPGroup hz2 hzN)
    rw [← heq]
    exact mem_sup_right (mem_zpowers z)
  have hT₀L : T₀ ≤ L := h.le_of_isPGroup hT₀N.le hT₀N.isPGroup
  have hT₀X : IsSylowOf 2 T₀ ⊤ := by
    obtain ⟨Q, hQ⟩ := hT₀N.isPGroup.exists_le_sylow
    rcases eq_or_lt_of_le hQ with hQe | hlt
    · rw [isSylowOf_iff]
      refine ⟨le_top, hT₀N.isPGroup, ?_⟩
      rw [relIndex_top_right, hQe]
      exact Q.not_dvd_index
    · exfalso
      have hnil : Group.IsNilpotent (Q : Subgroup X) := Q.isPGroup'.isNilpotent
      have hW : T₀.subgroupOf (Q : Subgroup X) < ⊤ := by
        refine lt_of_le_of_ne le_top fun hW => (ne_of_lt hlt) (le_antisymm hQ fun x hx => ?_)
        have : (⟨x, hx⟩ : (Q : Subgroup X)) ∈ T₀.subgroupOf (Q : Subgroup X) := hW ▸ mem_top _
        exact this
      obtain ⟨y, hyN, hyT⟩ := IsConcreteLE.exists_of_lt
        (Group.normalizerCondition_of_isNilpotent (G := (Q : Subgroup X)) _ hW)
      have hyN' : (y : X) ∈ normalizer (T₀ : Set X) := by
        rw [mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          have h1 := (mem_normalizer_iff.mp hyN ⟨x, hQ hx⟩).mp hx
          exact h1
        · intro hx
          have hxQ : x ∈ (Q : Subgroup X) := by
            have h1 : (y : X)⁻¹ * ((y : X) * x * (y : X)⁻¹) * y ∈ (Q : Subgroup X) :=
              mul_mem (mul_mem (inv_mem y.2) (hQ hx)) y.2
            rwa [show (y : X)⁻¹ * ((y : X) * x * (y : X)⁻¹) * y = x by group] at h1
          exact (mem_normalizer_iff.mp hyN ⟨x, hxQ⟩).mpr hx
      have hyL : (y : X) ∈ N := h.normalizer_le_of_conj_mem hT₀L
        (g := 1) (by rw [one_mul, inv_one, mul_one]; exact hzT₀) hyN'
      have hy2 : IsPGroup 2 (zpowers (y : X)) := Q.isPGroup'.to_le (zpowers_le.mpr y.2)
      have heq := hT₀N.eq_of_le le_sup_left (sup_le hT₀N.le (zpowers_le.mpr hyL))
        (IsPGroup.to_sup_of_normal_left' hT₀N.isPGroup hy2 (zpowers_le.mpr hyN'))
      have hyT₀ : (y : X) ∈ T₀ := by
        rw [← heq]
        exact mem_sup_right (mem_zpowers _)
      exact hyT hyT₀
  have hPN : P ≤ N := hPL.trans hLN
  obtain ⟨B, hB, hPB⟩ : ∃ B : Subgroup X, IsSylowOf 2 B N ∧ P ≤ B := by
    obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := N)).exists_le_sylow
    refine ⟨(Q : Subgroup N).map N.subtype, ⟨Q, rfl⟩, fun a ha => ?_⟩
    exact ⟨⟨a, hPN ha⟩, hQ ha, rfl⟩
  obtain ⟨m, hmN, hm⟩ := hT₀N.exists_mem_conj hB
  have hBeq : ∀ x, x ∈ B ↔ m⁻¹ * x * m ∈ T₀ := hm
  have hBL : B ≤ L := h.le_of_isPGroup hB.le hB.isPGroup
  have hBX : IsSylowOf 2 B ⊤ := by
    rw [isSylowOf_iff] at hT₀X ⊢
    obtain ⟨-, -, hidx⟩ := hT₀X
    refine ⟨le_top, hB.isPGroup, ?_⟩
    have hBc : B = T₀.map (MulAut.conj m).toMonoidHom := by
      ext x
      rw [hBeq, mem_map_equiv, MulAut.conj_symm_apply]
    rw [hBc, relIndex_top_right, index_map_of_injective _ (MulAut.conj m).injective,
      (MonoidHom.range_eq_top (f := (MulAut.conj m).toMonoidHom)).mpr (MulAut.conj m).surjective,
      index_top, mul_one]
    rwa [relIndex_top_right] at hidx
  rw [isSylowOf_iff, relIndex_top_right] at hBX
  refine ⟨hBX.2.1.toSylow hBX.2.2, by rw [IsPGroup.toSylow_coe]; exact hPB,
    by rw [IsPGroup.toSylow_coe]; exact hBL, m, ?_, ?_⟩
  · rw [IsPGroup.toSylow_coe, hBeq, show m⁻¹ * (m * z * m⁻¹) * m = z by group]
    exact hzT₀
  · intro s hs
    rw [IsPGroup.toSylow_coe, hBeq] at hs
    have h1 := mem_centralizer_singleton_iff.mp (hT₀z hs)
    calc s * (m * z * m⁻¹) = m * ((m⁻¹ * s * m) * z) * m⁻¹ := by group
      _ = m * (z * (m⁻¹ * s * m)) * m⁻¹ := by rw [h1]
      _ = m * z * m⁻¹ * s := by group

theorem exists_realize {P : Subgroup X} (hPL : P ≤ L) (hP : IsPGroup 2 P) {g : X}
    (hPg : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ L) :
    ∃ c ∈ normalizer (L : Set X), ∀ x ∈ P, c⁻¹ * x * c = g⁻¹ * x * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hPS, hSL, g₀, hg₀S, hg₀c⟩ := h.exists_sylow hPL hP
  obtain ⟨S', hP'S', hS'L, -⟩ := h.exists_sylow hPg (hP.map _)
  have hsyl : ∀ S'' : Sylow 2 X, (S'' : Subgroup X) ≤ L →
      IsSylowOf 2 (S'' : Subgroup X) (normalizer (L : Set X)) := fun S'' hS'' =>
    (isSylowOf_iff.mpr ⟨le_top, S''.isPGroup', by
      rw [relIndex_top_right]; exact S''.not_dvd_index⟩).of_le (hS''.trans le_normalizer) le_top
  obtain ⟨m, hmN, hm⟩ := (hsyl S hSL).exists_mem_conj (hsyl S' hS'L)
  have hPgm : P.map (MulAut.conj (g * m)⁻¹).toMonoidHom ≤ (S : Subgroup X) := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : g⁻¹ * x * g ∈ (S' : Subgroup X) :=
      hP'S' ⟨x, hx, by simp⟩
    have h2 := (hm _).mp h1
    simpa [mul_assoc] using h2
  obtain ⟨c₀, hc₀, hc₀P⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion S hPS hPgm
  have hc₀N : c₀ ∈ normalizer (L : Set X) := by
    clear hc₀P
    induction hc₀ with
    | one => exact one_mem _
    | @step c n Q _ hQ _ hn ih =>
      have hzQ : g₀ * z * g₀⁻¹ ∈ Q := by
        refine hQ.2.2.1 (mem_inf.mpr ⟨mem_centralizer_iff.mpr fun q hq => ?_, hg₀S⟩)
        exact hg₀c q (hQ.1 hq)
      exact mul_mem ih (h.normalizer_le_of_conj_mem (hQ.1.trans hSL) hzQ hn)
  refine ⟨c₀ * m⁻¹, mul_mem hc₀N (inv_mem hmN), fun x hx => ?_⟩
  have h1 := hc₀P x hx
  calc (c₀ * m⁻¹)⁻¹ * x * (c₀ * m⁻¹) = m * (c₀⁻¹ * x * c₀) * m⁻¹ := by group
    _ = m * ((g * m)⁻¹ * x * (g * m)) * m⁻¹ := by rw [h1]
    _ = g⁻¹ * x * g := by group

theorem isSylowOf_centralizer {u : X} (hu : u ∈ L) (hu2 : orderOf u = 2) {T : Subgroup X}
    (hT : IsSylowOf 2 T (normalizer (L : Set X) ⊓ centralizer ({u} : Set X))) :
    IsSylowOf 2 T (centralizer ({u} : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({u} : Set X) with hC
  have hTC : T ≤ C := hT.le.trans inf_le_right
  obtain ⟨P, hP, hTP⟩ : ∃ P : Subgroup X, IsSylowOf 2 P C ∧ T ≤ P := by
    obtain ⟨Q, hQ⟩ := (hT.isPGroup.comap_subtype (K := C)).exists_le_sylow
    refine ⟨(Q : Subgroup C).map C.subtype, ⟨Q, rfl⟩, fun a ha => ?_⟩
    exact ⟨⟨a, hTC ha⟩, hQ ha, rfl⟩
  have hu2' : IsPGroup 2 (zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2, pow_one])
  have huC : u ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have huP : u ∈ P := by
    have huN : zpowers u ≤ normalizer (P : Set X) := zpowers_le.mpr
      (centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun p hp =>
        (mem_centralizer_singleton_iff.mp (hP.le hp))))
    have heq := hP.eq_of_le le_sup_left (sup_le hP.le (zpowers_le.mpr huC))
      (IsPGroup.to_sup_of_normal_left' hP.isPGroup hu2' huN)
    rw [← heq]
    exact mem_sup_right (mem_zpowers u)
  obtain ⟨S, -, hSL, -⟩ := h.exists_sylow (zpowers_le.mpr hu) hu2'
  have hSX : IsSylowOf 2 (S : Subgroup X) ⊤ :=
    isSylowOf_iff.mpr ⟨le_top, S.isPGroup', by rw [relIndex_top_right]; exact S.not_dvd_index⟩
  obtain ⟨B, hB, hPB⟩ : ∃ B : Subgroup X, IsSylowOf 2 B ⊤ ∧ P ≤ B := by
    obtain ⟨Q, hQ⟩ := hP.isPGroup.exists_le_sylow
    exact ⟨Q, isSylowOf_iff.mpr ⟨le_top, Q.isPGroup', by
      rw [relIndex_top_right]; exact Q.not_dvd_index⟩, hQ⟩
  obtain ⟨k, -, hk⟩ := hSX.exists_mem_conj hB
  have hPk : ∀ x ∈ P, k⁻¹ * x * k ∈ L := fun x hx => hSL ((hk x).mp (hPB hx))
  obtain ⟨c, hcN, hc⟩ := h.exists_realize (zpowers_le.mpr hu) hu2' (g := k) (by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := hPk x (zpowers_le.mpr huP hx)
    simpa [MulAut.conj_apply] using h1)
  have hcu := hc u (mem_zpowers u)
  set d := k * c⁻¹ with hd
  have hdu : d * u * d⁻¹ = u := by
    calc d * u * d⁻¹ = k * c⁻¹ * u * (c * k⁻¹) := by rw [hd]; group
      _ = k * (c⁻¹ * u * c) * k⁻¹ := by group
      _ = u := by rw [hcu]; group
  set P' := P.map (MulAut.conj d⁻¹).toMonoidHom with hP'
  have hP'le : P' ≤ normalizer (L : Set X) ⊓ C := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine mem_inf.mpr ⟨le_normalizer ?_, ?_⟩
    · have h1 := hPk x hx
      have h2 : c * (k⁻¹ * x * k) * c⁻¹ ∈ L := (mem_normalizer_iff.mp hcN _).mp h1
      rwa [show c * (k⁻¹ * x * k) * c⁻¹ = d⁻¹ * x * d by rw [hd]; group] at h2
    · have hxC := hP.le hx
      rw [mem_centralizer_singleton_iff] at hxC ⊢
      have hdu' : d⁻¹ * u * d = u := by
        calc d⁻¹ * u * d = d⁻¹ * (d * u * d⁻¹) * d := by rw [hdu]
          _ = u := by group
      calc d⁻¹ * x * d * u = d⁻¹ * x * (d * u * d⁻¹) * d := by group
        _ = d⁻¹ * (x * u) * d := by rw [hdu]; group
        _ = d⁻¹ * (u * x) * d := by rw [hxC]
        _ = (d⁻¹ * u * d) * (d⁻¹ * x * d) := by group
        _ = u * (d⁻¹ * x * d) := by rw [hdu']
  have hcard : Nat.card P ≤ Nat.card T := by
    have hP'2 : IsPGroup 2 P' := hP.isPGroup.map _
    obtain ⟨k', -, hk'⟩ : ∃ k' ∈ normalizer (L : Set X) ⊓ C, ∀ a ∈ P', k'⁻¹ * a * k' ∈ T := by
      obtain ⟨B', hB', hP'B'⟩ : ∃ B' : Subgroup X,
          IsSylowOf 2 B' (normalizer (L : Set X) ⊓ C) ∧ P' ≤ B' := by
        obtain ⟨Q, hQ⟩ := (hP'2.comap_subtype (K := normalizer (L : Set X) ⊓ C)).exists_le_sylow
        refine ⟨(Q : Subgroup _).map (normalizer (L : Set X) ⊓ C).subtype, ⟨Q, rfl⟩,
          fun a ha => ?_⟩
        exact ⟨⟨a, hP'le ha⟩, hQ ha, rfl⟩
      obtain ⟨k', hk'N, hk'⟩ := hT.exists_mem_conj hB'
      exact ⟨k', hk'N, fun a ha => (hk' a).mp (hP'B' ha)⟩
    have hle : P'.map (MulAut.conj k'⁻¹).toMonoidHom ≤ T := by
      rintro _ ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply] using hk' a ha
    calc Nat.card P = Nat.card P' := by
          rw [hP', card_map_of_injective (MulAut.conj d⁻¹).injective]
      _ = Nat.card (P'.map (MulAut.conj k'⁻¹).toMonoidHom) :=
          (card_map_of_injective (MulAut.conj k'⁻¹).injective).symm
      _ ≤ Nat.card T := card_le_of_le hle
  have hTP' : T = P := eq_of_le_of_card_ge hTP hcard
  rw [hTP']
  exact hP

end Co1TwoCSetting

end CFSG.ComponentClassification.RankTwoExceptional.HoltFree
