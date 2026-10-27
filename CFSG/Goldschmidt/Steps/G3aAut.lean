module

public import CFSG.Goldschmidt.Steps.G3aBorel
import CFSG.Goldschmidt.Steps.GoldTypeBender
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectCentralAutomorphism

public section

namespace CFSG.Goldschmidt

open CFSG.Open
open scoped MatrixGroups Pointwise

namespace G3a

open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter
  sylowCenter_le AutControlAt)

section Simple

variable {X : Type} [Group X] [Finite X]

namespace BorelSetup

variable {T : Sylow 2 X} {D : Subgroup X} (h : BorelSetup T D)
include h

open CFSG.ComponentClassification.AschbacherToolkit.Bender in
theorem eq_conj [IsSimpleGroup X] (haut : AutControlAt (T : Subgroup X)) (φ : MulAut X)
    (hT : ∀ t ∈ (T : Subgroup X), φ t ∈ (T : Subgroup X))
    (hZ : ∀ z ∈ sylowCenter (T : Subgroup X), φ z = z)
    (hTZ : ∀ t ∈ (T : Subgroup X), t⁻¹ * φ t ∈ sylowCenter (T : Subgroup X)) :
    ∃ s ∈ (T : Subgroup X), φ = MulAut.conj s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := sylowCenter (T : Subgroup X) with hZdef
  have hpowZ : ∀ k : ℕ, ∀ z ∈ Z, (φ ^ k) z = z := by
    intro k
    induction k with
    | zero => intro z _; rfl
    | succ k ih => intro z hz; rw [pow_succ', MulAut.mul_apply, ih z hz, hZ z hz]
  have hpowTZ : ∀ k : ℕ, ∀ t ∈ (T : Subgroup X), t⁻¹ * (φ ^ k) t ∈ Z := by
    intro k
    induction k with
    | zero => intro t _; simp [Z.one_mem]
    | succ k ih =>
      intro t ht
      have hz := ih t ht
      have e : (φ ^ k) t = t * (t⁻¹ * (φ ^ k) t) := by group
      rw [pow_succ', MulAut.mul_apply, e, map_mul, hZ _ hz, ← mul_assoc]
      exact Z.mul_mem (hTZ t ht) hz
  obtain ⟨a, r, hr, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos φ).ne'
  set β := φ ^ (2 ^ a) with hβ
  have hβr : β ^ r = 1 := by rw [hβ, ← pow_mul, ← hn, pow_orderOf_eq_one]
  have hβT : ∀ t ∈ (T : Subgroup X), β t = t := by
    intro t ht
    have hz : t⁻¹ * β t ∈ Z := hpowTZ _ t ht
    have hpow : ∀ j : ℕ, (β ^ j) t = t * (t⁻¹ * β t) ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hβz : β (t⁻¹ * β t) = t⁻¹ * β t := hpowZ _ _ hz
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hβz,
          pow_succ' (t⁻¹ * β t) j, ← mul_assoc, mul_inv_cancel_left]
    have hzr : (t⁻¹ * β t) ^ r = 1 := by
      have h1 := hpow r
      rw [hβr, MulAut.one_apply] at h1
      exact mul_eq_left.mp h1.symm
    have hz1 := eq_one_of_pow_odd (sylowCenter_le _ hz) hr hzr
    rw [inv_mul_eq_one] at hz1
    exact hz1.symm
  obtain ⟨S₀, h₀⟩ := h.exists_ne_sylow
  have hβT' : β • T = T := Omega.smul_eq_of_mapsTo fun s hs => by rw [hβT s hs]; exact hs
  have hβS₀ : β • S₀ ≠ T := by
    intro hS
    apply h₀
    calc S₀ = β⁻¹ • (β • S₀) := (inv_smul_smul β S₀).symm
      _ = β⁻¹ • (β • T) := by rw [hS, hβT']
      _ = T := inv_smul_smul β T
  obtain ⟨r₀, hr₀, hr₀S⟩ := Omega.exists_smul_eq h.se h.card h₀ hβS₀
  have hpowS : ∀ j : ℕ, (β ^ j) • S₀ = r₀ ^ j • S₀ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', mul_smul, ih, Omega.smul_conj_smul, hβT _ ((T : Subgroup X).pow_mem hr₀ j),
        ← hr₀S, ← mul_smul, ← pow_succ]
  have h1 : r₀ ^ r • S₀ = S₀ := by rw [← hpowS r, hβr, one_smul]
  have h2 : r₀ ^ r = 1 := Omega.eq_one_of_mem_normalizer h.se h₀
    ((T : Subgroup X).pow_mem hr₀ r) (Sylow.smul_eq_iff_mem_normalizer.mp h1)
  have h3 : r₀ = 1 := eq_one_of_pow_odd hr₀ hr h2
  have hβS : β • S₀ = S₀ := by rw [← hr₀S, h3, one_smul]
  have hβ1 : β = 1 := Omega.eq_one_of_centralizes h.se h.card h₀ β hβT' hβS hβT
  by_contra hno
  push Not at hno
  obtain ⟨-, -, t, ht, hnot⟩ := haut φ hT hZ ⟨a, hβ1⟩ hno
  exact hnot (hTZ t ht)

end BorelSetup

end Simple

section Quasisimple

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem le_of_le_sup_center (P : Sylow 2 K) {Q : Subgroup K} (hQ : IsPGroup 2 Q)
    (hQP : Q ≤ (P : Subgroup K) ⊔ Subgroup.center K) : Q ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (P : Subgroup K) ⊔ Subgroup.center K ≤
      Subgroup.normalizer ((P : Subgroup K) : Set K) :=
    sup_le Subgroup.le_normalizer (Subgroup.center_le_normalizer _)
  have hp := hQ.to_sup_of_normal_right' P.isPGroup' (hQP.trans hN)
  have := P.is_maximal' hp le_sup_right
  rw [← this]
  exact le_sup_left

open CFSG.ComponentClassification.AschbacherToolkit.Bender in
theorem mem_normalizer_of_map (P : Sylow 2 K) {n : K}
    (hn : QuotientGroup.mk' (Subgroup.center K) n ∈ Subgroup.normalizer
      (((P : Subgroup K).map (QuotientGroup.mk' (Subgroup.center K)) : Subgroup _) : Set _)) :
    n ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (Subgroup.center K) with hπ
  have hle : (P : Subgroup K).map (MulAut.conj n).toMonoidHom ≤ P := by
    apply le_of_le_sup_center P (P.isPGroup'.map _)
    rintro _ ⟨t, ht, rfl⟩
    have h1 : π (n * t * n⁻¹) ∈ (P : Subgroup K).map π := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hn _).mp ⟨t, ht, rfl⟩
    have h2 : n * t * n⁻¹ ∈ ((P : Subgroup K).map π).comap π := h1
    rw [Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk'] at h2
    simpa [MulAut.conj_apply] using h2
  have hS := Omega.smul_eq_of_mapsTo (α := MulAut.conj n) (S := P) fun s hs => hle ⟨s, hs, rfl⟩
  rw [← Sylow.smul_def] at hS
  exact Sylow.smul_eq_iff_mem_normalizer.mp hS

theorem map_eq_sylowCenter
    (hI : IsGoldTypeI K) (P : Sylow 2 K) {A : Subgroup K}
    (hAP : A ≤ P) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcl : fusionStronglyClosed (A : Set K) P) (hAZ : ¬ A ≤ Subgroup.center K)
    {D : Subgroup (K ⧸ Subgroup.center K)}
    (h : BorelSetup (P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center K))) D) :
    A.map (QuotientGroup.mk' (Subgroup.center K)) =
      sylowCenter ((P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center K)) :
        Sylow 2 (K ⧸ Subgroup.center K)) : Subgroup (K ⧸ Subgroup.center K)) := by
  set π := QuotientGroup.mk' (Subgroup.center K) with hπ
  set P' : Sylow 2 (K ⧸ Subgroup.center K) := P.mapSurjective (QuotientGroup.mk'_surjective _)
    with hP'def
  have hP' : (P' : Subgroup _) = (P : Subgroup K).map π := Sylow.coe_mapSurjective _ _
  set A' := A.map π with hA'
  have hA'P : A' ≤ P' := by rw [hP']; exact Subgroup.map_mono hAP
  have hnorm : ∀ g ∈ Subgroup.normalizer
      ((P' : Subgroup (K ⧸ Subgroup.center K)) : Set (K ⧸ Subgroup.center K)),
      ∀ x ∈ A', g * x * g⁻¹ ∈ A' := by
    intro g hg x hx
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective _ g
    have hn := mem_normalizer_of_map P (by rw [← hP']; exact hg)
    obtain ⟨a, ha, rfl⟩ := hx
    have h1 : n * a * n⁻¹ ∈ (P : Subgroup K) := (Subgroup.mem_normalizer_iff.mp hn a).mp (hAP ha)
    have h2 : n * a * n⁻¹ ∈ A := by
      have := hcl a ha n⁻¹ (by simpa using h1)
      simpa using this
    exact ⟨n * a * n⁻¹, h2, by simp [π]⟩
  have hDA' : D ≤ Subgroup.normalizer (A' : Set (K ⧸ Subgroup.center K)) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hnorm d (h.le hd) x, fun hx => ?_⟩
    have := hnorm d⁻¹ (Subgroup.inv_mem _ (h.le hd)) _ hx
    simpa [mul_assoc] using this
  have hA'ne : A' ≠ ⊥ := by
    intro hb
    apply hAZ
    have := (Subgroup.map_eq_bot_iff _).mp hb
    rwa [hπ, QuotientGroup.ker_mk'] at this
  obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA'ne
  obtain ⟨k, hk2, hk1⟩ := BorelSetup.exists_involution_pow (T := P') (hA'P c.2) (by
    intro h'
    exact hc1 (Subtype.ext h'))
  have hck : (c : K ⧸ Subgroup.center K) ^ k ∈ A' := A'.pow_mem c.2 k
  have hcZ := h.inv _ (hA'P hck) hk2
  have hZA' : sylowCenter (P' : Subgroup _) ≤ A' := by
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]
      exact A'.one_mem
    obtain ⟨d, hd, rfl⟩ := h.trans hcZ hz hk1 hz1
    have := hnorm d⁻¹ (Subgroup.inv_mem _ (h.le hd)) _ hck
    simpa using this
  refine le_antisymm ?_ hZA'
  by_cases hab : IsMulCommutative (P' : Subgroup (K ⧸ Subgroup.center K))
  · intro x hx
    rw [mem_sylowCenter]
    refine ⟨hA'P hx, fun t ht => ?_⟩
    exact congrArg Subtype.val (hab.is_comm.comm ⟨t, ht⟩ ⟨x, hA'P hx⟩)
  · set P'' : Subgroup (K ⧸ Subgroup.center K) := (P' : Subgroup (K ⧸ Subgroup.center K))
      with hP''
    have hcase : (Nat.card P'' = Nat.card (sylowCenter P'') ^ 2 ∧
          Nat.card D = Nat.card (sylowCenter P'') - 1) ∨
        (Nat.card P'' = Nat.card (sylowCenter P'') ^ 3 ∧
          Nat.card D = (Nat.card (sylowCenter P'') ^ 2 - 1) /
            Nat.gcd 3 (Nat.card (sylowCenter P'') + 1)) := by
      rcases hI with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
      · exact absurd (GoldType.isMulCommutative_of_psl2_even (by omega) e P') hab
      · obtain ⟨hZc, hTc, hDc⟩ := h.orders_sz hn e
        left
        rw [hZc, hTc, hDc]
        exact ⟨rfl, rfl⟩
      · obtain ⟨hZc, hTc, hDc⟩ := h.orders_psu3 hn e
        right
        rw [hZc, hTc, hDc]
        exact ⟨rfl, rfl⟩
    rcases h.eq_or_eq_of_invariant hcase hZA' hA'P hDA' with heq | heq
    · exact heq.le
    · exfalso
      apply hab
      refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
      have hx : (x : K ⧸ Subgroup.center K) ∈ A' := by rw [heq]; exact x.2
      have hy : (y : K ⧸ Subgroup.center K) ∈ A' := by rw [heq]; exact y.2
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨b, hb, hby⟩ := hy
      change (x : K ⧸ Subgroup.center K) * y = y * x
      rw [← hax, ← hby, ← map_mul, ← map_mul, hAc a ha b hb]

end Quasisimple

theorem exists_sylow_of_fusionIsSylowIn {G : Type} [Group G] {T X : Subgroup G}
    (hTX : fusionIsSylowIn 2 T X) : ∃ P : Sylow 2 X, (P : Subgroup X) = T.subgroupOf X := by
  obtain ⟨hTX, hT, hmax⟩ := hTX
  refine ⟨⟨T.subgroupOf X, hT.comap_subtype, fun {Q} hQ hTQ => ?_⟩, rfl⟩
  have h1 := hmax (Q.map X.subtype) (Subgroup.map_subtype_le Q) (hQ.map X.subtype) fun s hs =>
    ⟨⟨s, hTX hs⟩, hTQ (show (⟨s, hTX hs⟩ : X) ∈ T.subgroupOf X from hs), rfl⟩
  rw [← h1]
  exact (Subgroup.comap_map_eq_self_of_injective X.subtype_injective Q).symm

end G3a

open G3a CFSG.ComponentClassification.AschbacherToolkit.Bender in
theorem G33 : S_G33 := by
  intro G _ _ L A T hLn hLq hI hS hAL hT hAT α hαA hαT hαTA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hLn
  obtain ⟨-, hAc, T₀, hT₀, hAT₀, hcl₀, -⟩ := hS
  obtain ⟨P₀, hP₀⟩ := exists_sylow_of_fusionIsSylowIn hT₀
  obtain ⟨P, hP⟩ := exists_sylow_of_fusionIsSylowIn hT
  set A' := A.subgroupOf L with hA'
  have hA'P₀ : A' ≤ P₀ := by
    rw [hP₀]
    exact fun x hx => hAT₀ hx
  have hA'P : A' ≤ P := by
    rw [hP]
    exact fun x hx => hAT hx
  have hcl₀' : fusionStronglyClosed (A' : Set L) (P₀ : Subgroup L) := by
    intro a ha g hg
    have hg' : g⁻¹ * a * g ∈ (P₀ : Subgroup L) := hg
    rw [hP₀] at hg'
    exact hcl₀ a ha g g.2 hg'
  have hcl' : fusionStronglyClosed (A' : Set L) (P : Subgroup L) :=
    stronglyClosed_of_le_sylow P₀ P hcl₀' hA'P
  have hAc' : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
    intro a ha b hb
    have := congrArg Subtype.val (hAc.is_comm.comm ⟨(a : G), ha⟩ ⟨(b : G), hb⟩)
    exact Subtype.ext this
  have hQ : fusionIsBenderGroup (L ⧸ Subgroup.center L) := by
    rcases hI with ⟨n, hn, he⟩ | ⟨n, hn, he⟩ | ⟨n, hn, he⟩
    · exact Or.inl ⟨n, by omega, he⟩
    · exact Or.inr (Or.inr ⟨n, hn, he⟩)
    · exact Or.inr (Or.inl ⟨n, hn, he⟩)
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hLq.2
  have hAZ : ¬ A' ≤ Subgroup.center L := by
    intro hle
    have hcl : Subgroup.normalClosure (A' : Set L) ≤ Subgroup.center L :=
      Subgroup.normalClosure_le_normal hle
    have htop : Subgroup.center L = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : (x : G) ∈ normalClosureIn L A := by rw [hAL]; exact x.2
      obtain ⟨y, hy, hyx⟩ := hx
      rw [show y = x from Subtype.ext hyx] at hy
      exact hcl hy
    have hsub : Subsingleton (L ⧸ Subgroup.center L) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    exact not_subsingleton _ hsub
  set π := QuotientGroup.mk' (Subgroup.center L) with hπ
  set P' : Sylow 2 (L ⧸ Subgroup.center L) := P.mapSurjective (QuotientGroup.mk'_surjective _)
    with hP'def
  have hP' : (P' : Subgroup (L ⧸ Subgroup.center L)) = (P : Subgroup L).map π :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨D, h⟩ := exists_borelSetup hQ P'
  have hK1 := map_eq_sylowCenter hI P hA'P hAc' hcl' hAZ h
  set φ : MulAut L := MulAut.conjNormal α⁻¹ with hφdef
  have hφ : ∀ x : L, ((φ x : L) : G) = α⁻¹ * x * α := fun x => by
    rw [hφdef, MulAut.conjNormal_apply, inv_inv]
  have hchar : (Subgroup.center L).map φ.toMonoidHom = Subgroup.center L :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance φ
  set φ' : MulAut (L ⧸ Subgroup.center L) :=
    QuotientGroup.congr (Subgroup.center L) (Subgroup.center L) φ hchar with hφ'def
  have hφ' : ∀ x : L, φ' (π x) = π (φ x) := fun x => rfl
  have hTφ : ∀ p ∈ (P : Subgroup L), φ p ∈ (P : Subgroup L) := by
    intro p hp
    rw [hP] at hp ⊢
    rw [Subgroup.mem_subgroupOf, hφ]
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hαT) p).mp hp
    rwa [inv_inv] at this
  have hT' : ∀ t ∈ (P' : Subgroup (L ⧸ Subgroup.center L)),
      φ' t ∈ (P' : Subgroup (L ⧸ Subgroup.center L)) := by
    intro t ht
    rw [hP'] at ht ⊢
    obtain ⟨p, hp, rfl⟩ := ht
    exact ⟨φ p, hTφ p hp, (hφ' p).symm⟩
  have hZ' : ∀ z ∈ sylowCenter (P' : Subgroup (L ⧸ Subgroup.center L)), φ' z = z := by
    intro z hz
    rw [← hK1] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    rw [hφ']
    congr 1
    apply Subtype.ext
    rw [hφ]
    have hc : (a : G) * α = α * a := Subgroup.mem_centralizer_iff.mp hαA a ha
    calc α⁻¹ * a * α = α⁻¹ * ((a : G) * α) := by group
      _ = α⁻¹ * (α * a) := by rw [hc]
      _ = a := by group
  have hTZ' : ∀ t ∈ (P' : Subgroup (L ⧸ Subgroup.center L)),
      t⁻¹ * φ' t ∈ sylowCenter (P' : Subgroup (L ⧸ Subgroup.center L)) := by
    intro t ht
    rw [hP'] at ht
    obtain ⟨p, hp, rfl⟩ := ht
    rw [hφ', ← map_inv, ← map_mul, ← hK1]
    refine ⟨p⁻¹ * φ p, ?_, rfl⟩
    have hpT : (p : G) ∈ T := by
      have := hp
      rw [hP] at this
      exact this
    have hxL : α⁻¹ * (p : G) * α * (p : G)⁻¹ ∈ L := by
      have h1 : α⁻¹ * p * α ∈ L := by
        have := hLn.conj_mem _ p.2 α⁻¹
        rwa [inv_inv] at this
      exact L.mul_mem h1 (L.inv_mem p.2)
    set x : L := ⟨α⁻¹ * (p : G) * α * (p : G)⁻¹, hxL⟩ with hxdef
    have hx : x ∈ A' := hαTA p hpT
    have hconj := conj_mem_of_stronglyClosed hA'P hcl' hp hx
    have e : p⁻¹ * x * p = p⁻¹ * φ p := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hxdef]
      rw [hφ]
      group
    rwa [e] at hconj
  obtain ⟨s', hs', hφs⟩ := h.eq_conj
    ((CFSG.ComponentClassification.AschbacherToolkit.BenderExt.benderData_of_isBenderGroup
      hQ).aut P') φ' hT' hZ' hTZ'
  rw [hP'] at hs'
  obtain ⟨s, hs, rfl⟩ := hs'
  have hψ : MulAut.conjNormal (α * (s : G))⁻¹ = (1 : MulAut L) := by
    apply CFSG.GorensteinWalter.perfect_central_automorphism_eq ⟨hLq.1⟩
    intro x
    rw [MulAut.one_apply, ← QuotientGroup.ker_mk' (Subgroup.center L), MonoidHom.mem_ker]
    have e1 : (MulAut.conjNormal (α * (s : G))⁻¹ x : L) = s⁻¹ * φ x * s := by
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hφ]
      group
    rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, ← hπ, ← hφ', hφs, MulAut.conj_apply]
    group
  have hc : α * (s : G) ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun f : MulAut L => ((f ⟨x, hx⟩ : L) : G)) hψ
    simp only [MulAut.conjNormal_apply, MulAut.one_apply, inv_inv] at h1
    calc x * (α * s) = (α * s) * ((α * (s : G))⁻¹ * x * (α * s)) := by group
      _ = (α * s) * x := by rw [h1]
  have hsT : (s : G) ∈ T := by
    have := hs
    rw [hP] at this
    exact this
  have e : α = (α * (s : G)) * (s : G)⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left (T.inv_mem hsT))

end CFSG.Goldschmidt
