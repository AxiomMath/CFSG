module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4N0StructOdd

public section

namespace CFSG.OddStandard.AltStdSmall4.N0

open Subgroup Equiv Equiv.Perm AltStdCycTwo

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ}

structure SetupData (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (z : G) (P O : Subgroup G)
    (s : G) : Prop where
  P_le : P ≤ D0 θ hn z
  P_pgroup : IsPGroup 2 P
  B0_le : B0 θ hn z ≤ P
  O_le : O ≤ C0 θ hn z
  O_odd : Odd (Nat.card O)
  O_norm : ∀ g ∈ N0 θ hn z, ∀ o ∈ O, g * o * g⁻¹ ∈ O
  decomp : ∀ d ∈ D0 θ hn z, ∃ p ∈ P, ∃ o ∈ O, d = p * o
  frattini : ∀ g ∈ N0 θ hn z, ∃ d ∈ D0 θ hn z, d⁻¹ * g ∈ normalizer (P : Set G)
  s_N0 : s ∈ N0 θ hn z
  s_norm : s ∈ normalizer (P : Set G)
  s_comm : s * z = z * s
  s_conj : ∀ i, s * eps θ hn i * s⁻¹ = eps θ hn (mPerm i)

section Config

variable [Finite G] {Q : Subgroup G} {θ : L ≃* alternatingGroup (Fin n)} {z : G}
  (hn : 8 ≤ n) (c : Config G L Q n θ z)

include c

theorem comm_z_mem_E {d : G} (hd : d ∈ N0 θ hn z) : d * z * d⁻¹ * z⁻¹ ∈ E θ hn := by
  obtain ⟨j, hj⟩ := conj_z_eq hn c hd
  rw [hj, ← eps_comm_z hn c j, mul_inv_cancel_right]
  exact eps_mem_E θ hn j

theorem E_comm {x y : G} (hx : x ∈ E θ hn) (hy : y ∈ E θ hn) : x * y = y * x := by
  obtain ⟨i, rfl⟩ := (mem_E_iff θ hn x).1 hx
  obtain ⟨j, rfl⟩ := (mem_E_iff θ hn y).1 hy
  exact eps_comm θ hn i j

variable (hF : ∃ g ∈ N0 θ hn z, g * z * g⁻¹ = z * w θ hn)

include hF

theorem card_D0 : Nat.card (D0 θ hn z) = Nat.card (C0 θ hn z) * 8 := by
  have hmem : ∀ d : D0 θ hn z, (d : G) * z * (d : G)⁻¹ * z⁻¹ ∈ E θ hn :=
    fun d => comm_z_mem_E hn c (Subgroup.mem_inf.1 d.2).1
  let β : D0 θ hn z →* E θ hn := MonoidHom.mk' (fun d => ⟨_, hmem d⟩) (by
    intro a b
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    set u := (b : G) * z * (b : G)⁻¹ * z⁻¹ with hu
    set v := (a : G) * z * (a : G)⁻¹ * z⁻¹ with hv
    have hau : (a : G) * u = u * a :=
      ((mem_centralizer_iff.1 (Subgroup.mem_inf.1 a.2).2) u (hmem b)).symm
    have huv : u * v = v * u := E_comm hn c (hmem b) (hmem a)
    calc (a : G) * b * z * ((a : G) * b)⁻¹ * z⁻¹ = (a : G) * u * (z * (a : G)⁻¹ * z⁻¹) := by
          rw [hu]; group
      _ = u * a * (z * (a : G)⁻¹ * z⁻¹) := by rw [hau]
      _ = u * v := by rw [hv]; group
      _ = v * u := huv)
  have hker : β.ker = (C0 θ hn z).subgroupOf (D0 θ hn z) := by
    ext d
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_C0_iff hn c]
    constructor
    · intro h
      have h1 : (d : G) * z * (d : G)⁻¹ * z⁻¹ = 1 := congrArg Subtype.val h
      refine ⟨(mem_centralizer_E_iff θ hn d).1 (Subgroup.mem_inf.1 d.2).2, ?_⟩
      calc (d : G) * z = (d : G) * z * (d : G)⁻¹ * z⁻¹ * (z * d) := by group
        _ = z * d := by rw [h1, one_mul]
    · rintro ⟨-, h2⟩
      apply Subtype.ext
      change (d : G) * z * (d : G)⁻¹ * z⁻¹ = 1
      rw [h2]
      group
  have hrange : β.range = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    obtain ⟨j, rfl⟩ := (mem_E_iff θ hn y).1 hy
    obtain ⟨d, hd, hdz⟩ := exists_D0_conj_z_eq hn c hF j
    refine ⟨⟨d, hd⟩, Subtype.ext ?_⟩
    change d * z * d⁻¹ * z⁻¹ = eps θ hn j
    rw [hdz, ← eps_comm_z hn c j, mul_inv_cancel_right]
  have h1 := Subgroup.card_ker_mul_card_range β
  rw [hker, hrange, Subgroup.card_top, card_E,
    Nat.card_congr (subgroupOfEquivOfLe (C0_le_D0 hn c)).toEquiv] at h1
  exact h1.symm

theorem exists_setup : ∃ P O : Subgroup G, ∃ s : G, SetupData θ hn z P O s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨O, hOC, hOodd, hOnorm, a, ha⟩ := exists_O0 hn c
  have hD := card_D0 hn c hF
  rw [ha] at hD
  have hD' : Nat.card (D0 θ hn z) = 2 ^ (a + 3) * Nat.card O := by
    rw [hD, pow_add]; ring
  obtain ⟨S⟩ : Nonempty (Sylow 2 (D0 θ hn z)) := inferInstance
  set P : Subgroup G := (S : Subgroup (D0 θ hn z)).map (D0 θ hn z).subtype with hPdef
  have hPD : P ≤ D0 θ hn z := map_subtype_le _
  have hfact : (Nat.card (D0 θ hn z)).factorization 2 = a + 3 := by
    rw [hD', Nat.factorization_mul (by positivity) (Nat.odd_iff.1 hOodd |> fun h => by omega),
      Nat.Prime.factorization_pow Nat.prime_two]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    rw [Nat.factorization_eq_zero_of_not_dvd (by
      rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hOodd)]
  have hScard : Nat.card S = 2 ^ (a + 3) := by
    rw [Sylow.card_eq_multiplicity, hfact]
  have hPcard : Nat.card P = 2 ^ (a + 3) := by
    rw [hPdef, card_map_of_injective (D0 θ hn z).subtype_injective, hScard]
  have hPS : Nat.card P = 2 ^ (Nat.card (D0 θ hn z)).factorization 2 := by
    rw [hPcard, hfact]
  have hPO : P ⊓ O = ⊥ := by
    apply inf_eq_bot_of_coprime
    rw [hPcard]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hOodd)
  have hOD : O ≤ D0 θ hn z := hOC.trans (C0_le_D0 hn c)
  have hdecomp : ∀ d ∈ D0 θ hn z, ∃ p ∈ P, ∃ o ∈ O, d = p * o := by
    let φ : P × O → D0 θ hn z := fun x => ⟨(x.1 : G) * x.2, mul_mem (hPD x.1.2) (hOD x.2.2)⟩
    have hφ : Function.Injective φ := by
      rintro ⟨p, o⟩ ⟨p', o'⟩ h
      have h1 : (p : G) * o = p' * o' := congrArg Subtype.val h
      have h2 : (p' : G)⁻¹ * p = o' * (o : G)⁻¹ := by
        calc (p' : G)⁻¹ * p = (p' : G)⁻¹ * (p * o) * (o : G)⁻¹ := by group
          _ = (p' : G)⁻¹ * (p' * o') * (o : G)⁻¹ := by rw [h1]
          _ = o' * (o : G)⁻¹ := by group
      have h3 : (p' : G)⁻¹ * p ∈ P ⊓ O :=
        Subgroup.mem_inf.2 ⟨mul_mem (inv_mem p'.2) p.2, h2 ▸ mul_mem o'.2 (inv_mem o.2)⟩
      rw [hPO, mem_bot] at h3
      have hp : (p : G) = p' := by
        have := congrArg ((p' : G) * ·) h3
        simpa using this
      have ho : (o : G) = o' := by
        rw [hp] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext hp) (Subtype.ext ho)
    have hbij : Function.Bijective φ := hφ.bijective_of_nat_card_le (by
      rw [Nat.card_prod, hPcard, hD'])
    intro d hd
    obtain ⟨⟨p, o⟩, hpo⟩ := hbij.2 ⟨d, hd⟩
    exact ⟨p, p.2, o, o.2, (congrArg Subtype.val hpo).symm⟩
  have hBP : B0 θ hn z ≤ P := by
    have hN : ((B0 θ hn z).subgroupOf (D0 θ hn z)).Normal := ⟨fun x hx g => by
      rw [mem_subgroupOf] at hx ⊢
      exact (mem_normalizer_iff.1 (Subgroup.mem_inf.1 g.2).1 _).1 hx⟩
    have hp : IsPGroup 2 ((B0 θ hn z).subgroupOf (D0 θ hn z)) := by
      intro x
      refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
      simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
      rw [sq]
      exact B0_sq hn c (mem_subgroupOf.1 x.2)
    have hle := hp.le_sylow_of_normal S
    intro x hx
    exact ⟨⟨x, B0_le_D0 hn c hx⟩, hle (by rw [mem_subgroupOf]; exact hx), rfl⟩
  have hfr : ∀ g ∈ N0 θ hn z, ∃ d ∈ D0 θ hn z, d⁻¹ * g ∈ normalizer (P : Set G) := by
    intro g hg
    set Qg : Subgroup G := P.map (MulAut.conj g).toMonoidHom with hQg
    have hQD : Qg ≤ D0 θ hn z := by
      rintro _ ⟨x, hx, rfl⟩
      exact conj_mem_D0 hn c hF hg (hPD hx)
    have hQcard : Nat.card (Qg.subgroupOf (D0 θ hn z)) =
        2 ^ (Nat.card (D0 θ hn z)).factorization 2 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hQD).toEquiv, hQg,
        card_map_of_injective (MulAut.conj g).injective, hPS]
    set Q₁ := Sylow.ofCard _ hQcard with hQ₁
    obtain ⟨d, hd⟩ := MulAction.exists_smul_eq (D0 θ hn z) S Q₁
    refine ⟨d, d.2, ?_⟩
    have hmemQ₁ : ∀ y : D0 θ hn z, y ∈ (Q₁ : Subgroup (D0 θ hn z)) ↔ (y : G) ∈ Qg := by
      intro y
      rw [hQ₁, Sylow.coe_ofCard, mem_subgroupOf]
    have hmemS : ∀ y : D0 θ hn z, y ∈ (S : Subgroup (D0 θ hn z)) ↔ (y : G) ∈ P := by
      intro y
      rw [hPdef]
      constructor
      · intro h
        exact ⟨y, h, rfl⟩
      · rintro ⟨y', hy', hyy'⟩
        rwa [Subtype.ext hyy'] at hy'
    have hsmul : ∀ y : D0 θ hn z, y ∈ ((d • S : Sylow 2 (D0 θ hn z)) : Subgroup (D0 θ hn z)) ↔
        d⁻¹ * y * d ∈ (S : Subgroup (D0 θ hn z)) := by
      intro y
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        ← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
    rw [mem_normalizer_iff]
    intro x
    have hconj : ((d : G)⁻¹ * g) * x * ((d : G)⁻¹ * g)⁻¹ = (d : G)⁻¹ * (g * x * g⁻¹) * d := by
      group
    rw [hconj]
    constructor
    · intro hx
      have hy : g * x * g⁻¹ ∈ Qg := ⟨x, hx, rfl⟩
      have hyD : g * x * g⁻¹ ∈ D0 θ hn z := hQD hy
      have h1 : (⟨g * x * g⁻¹, hyD⟩ : D0 θ hn z) ∈ (Q₁ : Subgroup (D0 θ hn z)) :=
        (hmemQ₁ _).2 hy
      rw [← hd, hsmul] at h1
      have := (hmemS _).1 h1
      exact this
    · intro hx
      have hyD : g * x * g⁻¹ ∈ D0 θ hn z := by
        have h1 := hPD hx
        have h2 : g * x * g⁻¹ = (d : G) * ((d : G)⁻¹ * (g * x * g⁻¹) * d) * (d : G)⁻¹ := by
          group
        rw [h2]
        exact mul_mem (mul_mem d.2 h1) (inv_mem d.2)
      have h1 : (d⁻¹ * ⟨g * x * g⁻¹, hyD⟩ * d : D0 θ hn z) ∈ (S : Subgroup (D0 θ hn z)) :=
        (hmemS _).2 hx
      rw [← hsmul, hd, hmemQ₁] at h1
      obtain ⟨x', hx', hxx'⟩ := h1
      have : x' = x := by
        have := congrArg (fun y => g⁻¹ * y * g) hxx'
        simpa [MulAut.conj_apply, mul_assoc] using this
      rw [← this]
      exact hx'
  obtain ⟨d, hd, hdN⟩ := hfr _ (sg_mem_N0 hn c)
  obtain ⟨p, hp, o, ho, rfl⟩ := hdecomp d hd
  set t := p * o⁻¹ * p⁻¹ with ht
  have htO : t ∈ O := hOnorm p (Subgroup.mem_inf.1 (hPD hp)).1 _ (inv_mem ho)
  obtain ⟨htE, htz⟩ := (mem_C0_iff hn c t).1 (hOC htO)
  have hs : p * ((p * o)⁻¹ * sg θ hn) = t * sg θ hn := by rw [ht]; group
  refine ⟨P, O, t * sg θ hn, ⟨hPD, S.isPGroup'.map _, hBP, hOC, hOodd, hOnorm, hdecomp, hfr,
    ?_, ?_, ?_, ?_⟩⟩
  · exact mul_mem ((C0_le_N0 hn c) (hOC htO)) (sg_mem_N0 hn c)
  · rw [← hs]
    exact mul_mem (le_normalizer hp) hdN
  · rw [mul_assoc, sg_comm_z hn c, ← mul_assoc, htz, mul_assoc]
  · intro i
    calc t * sg θ hn * eps θ hn i * (t * sg θ hn)⁻¹
        = t * (sg θ hn * eps θ hn i * (sg θ hn)⁻¹) * t⁻¹ := by group
      _ = t * eps θ hn (mPerm i) * t⁻¹ := by rw [sg_conj_eps]
      _ = eps θ hn (mPerm i) := by rw [htE, mul_inv_cancel_right]

end Config

end CFSG.OddStandard.AltStdSmall4.N0
