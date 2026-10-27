module

public import CFSG.GH74.GLS.IVK.L2.TShape
public import CFSG.GH74.GLS.IVK.L2.Lemma12
public import CFSG.CharacterTheory.Semidihedral.ProjectiveSL2Cover

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter
open CFSG.Semidihedral

section Lemma19Basics

variable {H : Type} [Group H] (Khat : Subgroup H) [Khat.Normal] {F : Type} [Field F]

theorem exists_z (hC : centralizer (Khat : Set H) ≤ Khat)
    (φ : ↥Khat ≃* Matrix.SpecialLinearGroup (Fin 2) F) (h2 : (2 : F) ≠ 0) :
    ∃ z : H, z ∈ Khat ∧ z ≠ 1 ∧ z * z = 1 ∧ (∀ x ∈ Khat, x * x = 1 → x = 1 ∨ x = z) ∧
      (∀ h : H, h * z = z * h) ∧ (∀ g ∈ center H, g = 1 ∨ g = z) := by
  set z₀ : ↥Khat := φ.symm (OddFieldSL2.minusIdentity F) with hz₀
  have hφz : φ z₀ = OddFieldSL2.minusIdentity F := φ.apply_symm_apply _
  have hz1 : z₀ ≠ 1 := by
    intro h
    have := OddFieldSL2.minusIdentity_ne_one F h2
    apply this
    rw [← hφz, h, map_one]
  have hzz : z₀ * z₀ = 1 := by
    apply φ.injective
    rw [map_mul, hφz, map_one, ← pow_two]
    exact OddFieldSL2.minusIdentity_square F
  have huniq : ∀ x ∈ Khat, x * x = 1 → x = 1 ∨ x = (z₀ : H) := by
    intro x hx hx2
    have hinv : (φ ⟨x, hx⟩)⁻¹ = φ ⟨x, hx⟩ := by
      rw [← map_inv]
      congr 1
      apply Subtype.ext
      exact inv_eq_of_mul_eq_one_right hx2
    rcases OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self F h2 _ hinv with h1 | h1
    · left
      have : (⟨x, hx⟩ : ↥Khat) = 1 := φ.injective (by rw [h1, map_one])
      exact congrArg Subtype.val this
    · right
      have : (⟨x, hx⟩ : ↥Khat) = z₀ := φ.injective (by rw [h1, hφz])
      exact congrArg Subtype.val this
  have hcentral : ∀ h : H, h * (z₀ : H) = (z₀ : H) * h := by
    intro h
    have hmem : h * (z₀ : H) * h⁻¹ ∈ Khat := Subgroup.Normal.conj_mem ‹Khat.Normal› _ z₀.2 h
    have hsq : (h * (z₀ : H) * h⁻¹) * (h * (z₀ : H) * h⁻¹) = 1 := by
      calc (h * (z₀ : H) * h⁻¹) * (h * (z₀ : H) * h⁻¹) = h * ((z₀ : H) * (z₀ : H)) * h⁻¹ := by
            group
        _ = 1 := by
          have : (z₀ : H) * (z₀ : H) = 1 := congrArg Subtype.val hzz
          rw [this]; group
    rcases huniq _ hmem hsq with h1 | h1
    · exfalso
      apply hz1
      apply Subtype.ext
      have : (z₀ : H) = h⁻¹ * (h * (z₀ : H) * h⁻¹) * h := by group
      rw [this, h1]
      simp
    · calc h * (z₀ : H) = (h * (z₀ : H) * h⁻¹) * h := by group
        _ = (z₀ : H) * h := by rw [h1]
  have hcenter : ∀ g ∈ center H, g = 1 ∨ g = (z₀ : H) := by
    intro g hg
    have hgC : g ∈ centralizer (Khat : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k _
      exact (Subgroup.mem_center_iff.mp hg k)
    have hgK : g ∈ Khat := hC hgC
    have hcen : φ ⟨g, hgK⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [Subgroup.mem_center_iff]
      intro b
      obtain ⟨k, rfl⟩ := φ.surjective b
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp hg k
    rcases (ProjectiveSL2Cover.mem_center_iff_eq_one_or_minusIdentity F _).1 hcen with h1 | h1
    · left
      have : (⟨g, hgK⟩ : ↥Khat) = 1 := φ.injective (by rw [h1, map_one])
      exact congrArg Subtype.val this
    · right
      have : (⟨g, hgK⟩ : ↥Khat) = z₀ := φ.injective (by
        rw [h1, hφz, ProjectiveSL2Cover.minusIdentity_eq_neg_one]; rfl)
      exact congrArg Subtype.val this
  exact ⟨z₀, z₀.2, fun h => hz1 (Subtype.ext h), congrArg Subtype.val hzz, huniq, hcentral, hcenter⟩

end Lemma19Basics

section Lemma19c

theorem zpowers_normal_of_central {G : Type*} [Group G] {z : G} (hz : ∀ g, g * z = z * g) :
    (Subgroup.zpowers z).Normal :=
  ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have h0 : g * z * g⁻¹ = z := by
      calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [hz g]
        _ = z := by group
    have h1 : g * z ^ k * g⁻¹ = (g * z * g⁻¹) ^ k := (conj_zpow).symm
    rw [h1, h0]
    exact Subgroup.zpow_mem_zpowers z k⟩

theorem mul_comm_of_mem_zpowers_sup {G : Type*} [Group G] {q₀ z : G} (hz : ∀ g, g * z = z * g)
    {x y : G} (hx : x ∈ Subgroup.zpowers q₀ ⊔ Subgroup.zpowers z)
    (hy : y ∈ Subgroup.zpowers q₀ ⊔ Subgroup.zpowers z) : x * y = y * x := by
  have hzn : (Subgroup.zpowers z).Normal := zpowers_normal_of_central hz
  rw [Subgroup.mem_sup_of_normal_right] at hx hy
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hx
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx₁
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy₁
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx₂
  obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy₂
  have h1 : Commute q₀ z := hz q₀
  have hAC : Commute (q₀ ^ i) (q₀ ^ j) := Commute.zpow_zpow_self q₀ i j
  have hAD : Commute (q₀ ^ i) (z ^ l) := Commute.zpow_zpow h1 i l
  have hBC : Commute (z ^ k) (q₀ ^ j) := Commute.zpow_zpow h1.symm k j
  have hBD : Commute (z ^ k) (z ^ l) := Commute.zpow_zpow_self z k l
  exact Commute.mul_left (Commute.mul_right hAC hAD) (Commute.mul_right hBC hBD)

theorem ivk_1_9_c : IVK_1_9_c := by
  intro F _ _ hF H _ _ Khat _ hC hK hN T
  classical
  obtain ⟨eN⟩ := hN
  obtain ⟨hKS⟩ := hK
  have hodd : IsOddPrimePower (Nat.card F) := isOddPrimePower_of_L2Field hF
  have hodd' : Odd (Nat.card F) := hF.1
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd'
  let φ : ↥Khat ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    hKS.trans (specialLinearGroupEquivStatedSL 2 F).symm
  obtain ⟨z, hzK, hz1, hzz, hzu, hzc, hzcen⟩ := exists_z Khat hC φ h2
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzn : (Subgroup.zpowers z).Normal := zpowers_normal_of_central hzc
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo]; norm_num)
  have hzT : z ∈ (T : Subgroup H) := IsPGroup.le_sylow_of_normal hzp T (Subgroup.mem_zpowers z)
  have hcen : ∀ g : H, g ∈ center H ↔ g = 1 ∨ g = z := by
    intro g
    constructor
    · exact hzcen g
    · rintro (h | h)
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_center_iff.2 hzc
  set π : H →* H ⧸ center H := QuotientGroup.mk' (center H) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : ∀ t : H, π t = 1 ↔ t = 1 ∨ t = z := by
    intro t
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hcen]
  set Tb : Sylow 2 (H ⧸ center H) := T.mapSurjective hπ with hTb
  have hTbN : (Tb : Subgroup (H ⧸ center H)) ≤ oPrimeResidual 2 (H ⧸ center H) := by
    intro y hy
    rw [hTb, Sylow.coe_mapSurjective] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    obtain ⟨k, hk⟩ := (T.isPGroup') ⟨t, ht⟩
    exact Subgroup.subset_closure ⟨k, by
      rw [← map_pow]
      have : t ^ (2 ^ k) = 1 := congrArg Subtype.val hk
      rw [this, map_one]⟩
  set S : Sylow 2 ↥(oPrimeResidual 2 (H ⧸ center H)) := Tb.subtype hTbN with hS
  have hfinPGL : Finite (PGL2 F) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 2) F →* PGL2 F)
      Matrix.ProjGenLinGroup.mk_surjective
  have hdih := hasDihedralSylowTwo_of_equiv eN.symm (pgl2_odd_hasDihedralSylowTwo_model F hodd) S
  obtain ⟨m, hm1, ⟨eS⟩⟩ := hdih
  have hTbmem : ∀ t : ↥(T : Subgroup H), π t ∈ (Tb : Subgroup (H ⧸ center H)) := by
    intro t
    rw [hTb, Sylow.coe_mapSurjective]
    exact ⟨t, t.2, rfl⟩
  let f : ↥(T : Subgroup H) →* ↥(oPrimeResidual 2 (H ⧸ center H)) :=
    (π.comp (T : Subgroup H).subtype).codRestrict _ (fun t => hTbN (hTbmem t))
  have hfS : ∀ t : ↥(T : Subgroup H), f t ∈ S := by
    intro t
    show (f t : H ⧸ center H) ∈ (Tb : Subgroup (H ⧸ center H))
    exact hTbmem t
  let g : ↥(T : Subgroup H) →* ↥S := f.codRestrict S hfS
  let πT : ↥(T : Subgroup H) →* DihedralGroup (2 ^ m) := eS.toMonoidHom.comp g
  have hπTsurj : Function.Surjective πT := by
    intro d
    obtain ⟨t, htT, ht⟩ : ∃ t ∈ (T : Subgroup H),
        π t = (((eS.symm d : ↥S) : ↥(oPrimeResidual 2 (H ⧸ center H))) : H ⧸ center H) := by
      have hmem : (((eS.symm d : ↥S) : ↥(oPrimeResidual 2 (H ⧸ center H))) : H ⧸ center H) ∈
          (Tb : Subgroup (H ⧸ center H)) := (eS.symm d).2
      rw [hTb, Sylow.coe_mapSurjective] at hmem
      obtain ⟨t, ht, h⟩ := hmem
      exact ⟨t, ht, h⟩
    refine ⟨⟨t, htT⟩, ?_⟩
    show eS (g ⟨t, htT⟩) = d
    have : g ⟨t, htT⟩ = eS.symm d := Subtype.ext (Subtype.ext ht)
    rw [this]
    exact eS.apply_symm_apply d
  have hz1' : (⟨z, hzT⟩ : ↥(T : Subgroup H)) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hzz' : (⟨z, hzT⟩ : ↥(T : Subgroup H)) * ⟨z, hzT⟩ = 1 := Subtype.ext hzz
  have hker : ∀ t : ↥(T : Subgroup H), πT t = 1 ↔ t = 1 ∨ t = ⟨z, hzT⟩ := by
    intro t
    have h1 : πT t = 1 ↔ π t = 1 := by
      constructor
      · intro h
        have h' : g t = 1 := eS.injective (by rw [map_one]; exact h)
        exact congrArg (fun x : ↥S => ((x : ↥(oPrimeResidual 2 (H ⧸ center H))) : H ⧸ center H)) h'
      · intro h
        have h' : g t = 1 := Subtype.ext (Subtype.ext h)
        show eS (g t) = 1
        rw [h', map_one]
    rw [h1, hπker]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
  have hcardN : Nat.card ↥(oPrimeResidual 2 (H ⧸ center H)) =
      Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Nat.card_congr eN.toEquiv, pgl2_card_formula]
  have h8 : 2 ^ 3 ∣ Nat.card ↥(oPrimeResidual 2 (H ⧸ center H)) := by
    rw [hcardN]
    obtain ⟨a, ha⟩ := hodd'
    refine Dvd.dvd.mul_left ?_ _
    have h4 : Nat.card F ^ 2 - 1 = 4 * (a * (a + 1)) := by
      rw [ha]
      have : (2 * a + 1) ^ 2 = 4 * (a * (a + 1)) + 1 := by ring
      omega
    rw [h4]
    obtain ⟨c, hc⟩ := (Nat.even_mul_succ_self a).two_dvd
    exact ⟨c, by rw [hc]; ring⟩
  have hSdvd : 2 ^ 3 ∣ Nat.card ↥(S : Subgroup ↥(oPrimeResidual 2 (H ⧸ center H))) :=
    S.pow_dvd_card_of_pow_dvd_card h8
  have hSD : Nat.card ↥(S : Subgroup ↥(oPrimeResidual 2 (H ⧸ center H))) = 2 * 2 ^ m := by
    rw [Nat.card_congr eS.toEquiv, DihedralGroup.nat_card]
  have hm2 : 2 ≤ m := by
    rw [hSD] at hSdvd
    by_contra hlt
    have hm' : m ≤ 1 := by omega
    have h4 : 2 * 2 ^ m ≤ 4 := by
      calc 2 * 2 ^ m ≤ 2 * 2 ^ 1 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hm')
        _ = 4 := by norm_num
    have := Nat.le_of_dvd (by positivity) hSdvd
    omega
  obtain ⟨P, hP⟩ := CFSG.Glauberman.sylow_inf_normal (p := 2) T (N := Khat)
  have hKcard : Nat.card ↥Khat = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Nat.card_congr φ.toEquiv, sl2_card_formula]
  have hPS : Nat.card ↥(P : Subgroup ↥Khat) =
      Nat.card ↥(S : Subgroup ↥(oPrimeResidual 2 (H ⧸ center H))) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity, hKcard, hcardN]
  set Qc : Subgroup H := (T : Subgroup H) ⊓ Khat with hQc
  let Q : Subgroup ↥(T : Subgroup H) := Qc.subgroupOf (T : Subgroup H)
  have hQcard1 : Nat.card ↥Q = Nat.card ↥Qc :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Qc ≤ (T : Subgroup H))).toEquiv
  have hPcard1 : Nat.card ↥(P : Subgroup ↥Khat) = Nat.card ↥Qc := by
    rw [hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Qc ≤ Khat)).toEquiv
  have hQcardD : Nat.card ↥Q = 2 * 2 ^ m := by rw [hQcard1, ← hPcard1, hPS, hSD]
  have hTcard : Nat.card ↥(T : Subgroup H) = 2 * (2 * 2 ^ m) := by
    have h1 := Subgroup.card_ker_mul_card_range πT
    rw [card_ker_eq_two πT hz1' hzz' hker, MonoidHom.range_eq_top.2 hπTsurj, Subgroup.card_top,
      DihedralGroup.nat_card] at h1
    exact h1.symm
  have hQcard : Nat.card ↥Q * 2 = Nat.card ↥(T : Subgroup H) := by
    rw [hQcardD, hTcard]; ring
  have hzQ : (⟨z, hzT⟩ : ↥(T : Subgroup H)) ∈ Q := Subgroup.mem_subgroupOf.2 ⟨hzT, hzK⟩
  have hQu : ∀ x ∈ Q, x * x = 1 → x = 1 ∨ x = (⟨z, hzT⟩ : ↥(T : Subgroup H)) := by
    intro x hx hx2
    have hxK : (x : H) ∈ Khat := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).2
    have hx2' : (x : H) * (x : H) = 1 := congrArg Subtype.val hx2
    rcases hzu _ hxK hx2' with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hPmem : ∀ a : ↥Khat, a ∈ P → (a : H) ∈ (T : Subgroup H) := by
    intro a ha
    have h' : a ∈ (P : Subgroup ↥Khat) := ha
    rw [hP] at h'
    exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 h')).1
  have hQnc : ∀ q₀ : ↥(T : Subgroup H),
      ¬ Q ≤ Subgroup.zpowers q₀ ⊔ Subgroup.zpowers (⟨z, hzT⟩ : ↥(T : Subgroup H)) := by
    intro q₀ hle
    obtain ⟨a, b, haP, hbP, hab⟩ : ∃ a b : ↥Khat, a ∈ P ∧ b ∈ P ∧ a * b ≠ b * a := by
      obtain ⟨f, hf⟩ := CFSG.Semidihedral.OddFieldSL2.exists_quaternion_embedding_in_sylow F hodd'
        (P.mapSurjective (f := φ.toMonoidHom) φ.surjective)
      have hnc : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
          QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by decide
      have hu := (f (QuaternionGroup.a 1)).2
      have hv := (f (QuaternionGroup.xa 0)).2
      change _ ∈ Subgroup.map φ.toMonoidHom (P : Subgroup ↥Khat) at hu hv
      obtain ⟨a, haP, hau⟩ := hu
      obtain ⟨b, hbP, hbv⟩ := hv
      refine ⟨a, b, haP, hbP, fun h => hnc (hf ?_)⟩
      have hau' : φ a = (f (QuaternionGroup.a 1)).1 := hau
      have hbv' : φ b = (f (QuaternionGroup.xa 0)).1 := hbv
      have h' := congrArg φ h
      rw [map_mul, map_mul, hau', hbv'] at h'
      rw [map_mul, map_mul]
      exact Subtype.ext h'
    have haT := hPmem a haP
    have hbT := hPmem b hbP
    have haQ : (⟨(a : H), haT⟩ : ↥(T : Subgroup H)) ∈ Q := Subgroup.mem_subgroupOf.2 ⟨haT, a.2⟩
    have hbQ : (⟨(b : H), hbT⟩ : ↥(T : Subgroup H)) ∈ Q := Subgroup.mem_subgroupOf.2 ⟨hbT, b.2⟩
    have hcomm := mul_comm_of_mem_zpowers_sup (q₀ := q₀) (z := (⟨z, hzT⟩ : ↥(T : Subgroup H)))
      (fun g => Subtype.ext (hzc g.1)) (hle haQ) (hle hbQ)
    have hcomm' : (a : H) * (b : H) = (b : H) * (a : H) := congrArg Subtype.val hcomm
    exact hab (Subtype.ext hcomm')
  have hTsh := tshape (T := ↥(T : Subgroup H)) T.isPGroup' hm2 πT hπTsurj
    (z := ⟨z, hzT⟩) hz1' hzz' hker Q hzQ hQcard hQu hQnc
  exact hTsh.symm

end Lemma19c

end CFSG.GH74.GLS.IVK
