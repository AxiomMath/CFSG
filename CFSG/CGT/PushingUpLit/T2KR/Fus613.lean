module

public import CFSG.CGT.PushingUpLit.T2KR.FusSetup

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.T2K CFSG.CGT.Timmesfeld75 CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.JonesParshall
open scoped commutatorElement LinearAlgebra.Projectivization
open MData (QM)

variable {G : Type} [Group G] [Finite G]

namespace MData

variable {L M : Subgroup G} {n : ℕ} (H : MData G L M n)

include H in
theorem exists_conj_blockU {v₁ v₂ : G} (h₁ : v₁ ∈ blockU L) (h₂ : v₂ ∈ blockU L) (h₁1 : v₁ ≠ 1)
    (h₂1 : v₂ ≠ 1) : ∃ l ∈ L, l * v₁ * l⁻¹ = v₂ := by
  have hne : ∀ {v : G}, v ∈ blockU L → v ≠ 1 → H.D.ψe v ≠ 0 := by
    intro v hv hv1 h0
    apply hv1
    exact H.ψe_injOn hv (one_mem _) (by rw [h0, H.D.ψe_one])
  obtain ⟨g, hg⟩ := CFSG.CGT.PushingUpLit.Glue.exists_sl2_mulVec_eq_of_ne_zero (hne h₁ h₁1)
    (hne h₂ h₂1)
  obtain ⟨l, hl⟩ := H.D.φ_surj g
  refine ⟨l, l.2, ?_⟩
  have hlv : (l : G) * v₁ * (l : G)⁻¹ ∈ blockU L := conj_mem_blockU (Subgroup.le_normalizer l.2) h₁
  have key := H.D.ψ_conj l ⟨v₁, h₁⟩ hlv
  refine H.ψe_injOn hlv h₂ ?_
  rw [H.D.ψe_of_mem hlv, H.D.ψe_of_mem h₂, key, hl, toAdd_ofAdd, ← H.D.ψe_of_mem h₁, hg,
    H.D.ψe_of_mem h₂]

include H in
theorem QL_le_blockU_of_involution {ε : G} (hεL : ε ∈ L) (hε2 : ε * ε = 1)
    (hεQ : ε ∉ QM L M) : QM L M ⊓ L ≤ blockU L := by
  have hO : oTwoIn L = blockU L := by
    refine H.nat.oTwoIn_eq_blockU_of_sq_mem (r := ε) hεL ?_ ?_
    · intro hεO
      apply hεQ
      rw [← H.nat.inf_centralizer_blockU] at hεO
      exact ⟨H.le hεO.1, hεO.2⟩
    · rw [pow_two, hε2]
      exact (blockU L).one_mem
  intro y hy
  have hy' : y ∈ L ⊓ Subgroup.centralizer (blockU L : Set G) := ⟨hy.2, hy.1.2⟩
  rw [H.nat.inf_centralizer_blockU, hO] at hy'
  exact hy'

end MData

@[expose] def Print613 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ) (D : Subgroup G) (g : G)
    (hE1 : FooteNonsolvableSimple) (hs : Sit64 G L M T n D g),
    PairFacts (MData.ofSec6 hE1 hs.sec6) (normIn (QOf L M) (Aof L M g))
      (normIn (Aof L M g) (QOf L M)) D → Nat.card D = 4 →
      ∀ T' : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ → T' ≤ M → QOf L M ≤ T' →
        normIn (Aof L M g) (QOf L M) ≤ T' →
        ∀ x ∈ D, x ∉ blockU L → ∀ r ∈ normIn (Aof L M g) (QOf L M), r ∈ L → r ∉ QOf L M →
          ∃ z : G, z ∈ blockU L ∧ z ≠ 1 ∧ (∀ t ∈ T', t * z = z * t) ∧
            (∀ t ∈ T', t * t = 1 → t ≠ 1 → t ≠ z →
              t ∈ ⁅T' ⊓ Subgroup.centralizer ({t} : Set G),
                T' ⊓ Subgroup.centralizer ({t} : Set G)⁆ →
              ∀ u ∈ ⁅T' ⊓ Subgroup.centralizer ({t} : Set G),
                T' ⊓ Subgroup.centralizer ({t} : Set G)⁆, u = 1 ∨ u = t ∨ u = z ∨ u = t * z) ∧
            (z ∈ ⁅T' ⊓ Subgroup.centralizer ({x * r} : Set G),
                T' ⊓ Subgroup.centralizer ({x * r} : Set G)⁆ ∧
              ∃ w ∈ ⁅T' ⊓ Subgroup.centralizer ({x * r} : Set G),
                T' ⊓ Subgroup.centralizer ({x * r} : Set G)⁆, w ≠ 1 ∧ w ≠ z) ∧
            ⁅T', T'⁆ ≤ L

theorem print614_of_613 (h613 : Print613) : Print614 := by
  intro G _ _ L M T n D g hE1 hs hP hD4 x hxD hxV r hrB hrL hrQ h hh
  classical
  set H := MData.ofSec6 hE1 hs.sec6 with hH
  set B := normIn (Aof L M g) (QOf L M) with hB
  have hB2 : IsPGroup 2 B := isPGroup_two_of_sq_eq_one hP.B_sq
  obtain ⟨k, hkM, hk⟩ := exists_conj_le_of_isPGroup hs.sec6.sec4.sylow hB2 hP.B_le_M
  set T' : Subgroup G := T.map (MulAut.conj k⁻¹).toMonoidHom with hT'
  have hBT' : B ≤ T' := by
    intro y hy
    refine ⟨k * y * k⁻¹, hk ⟨y, hy, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hT'M : T' ≤ M := by
    rintro _ ⟨t, ht, rfl⟩
    have htM : t ∈ M := hs.sec6.sec4.sylow.le ht
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact M.mul_mem (M.mul_mem (M.inv_mem hkM) htM) hkM
  have hT'syl : CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
    rw [hT', card_map_conj]
    exact hs.sec6.sec4.sylowG.card_eq
  have hQT' : QOf L M ≤ T' := by
    intro q hq
    have hkq : k * q * k⁻¹ ∈ QOf L M := by
      have hk' : k ∈ Subgroup.normalizer ((QOf L M : Subgroup G) : Set G) := by
        rw [hs.sec6.N_Q]; exact hkM
      exact (Subgroup.mem_normalizer_iff.1 hk' q).1 hq
    refine ⟨k * q * k⁻¹, hs.sec6.Q_le_T hkq, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  obtain ⟨z, hzV, hz1, hzc, hA, ⟨hzC, w, hwC, hw1, hwz⟩, hL⟩ :=
    h613 G L M T n D g hE1 hs hP hD4 T' hT'syl hT'M hQT' hBT' x hxD hxV r hrB hrL hrQ
  have hxB : x ∈ B := hP.D_le_B hxD
  have hx2 : x * x = 1 := hP.B_sq x hxB
  have hr2 : r * r = 1 := hP.B_sq r hrB
  have hxr : x * r = r * x := hP.B_comm x hxB r hrB
  have hxQ : x ∈ QM L M := hP.D_le_Q hxD
  have hQL : QM L M ⊓ L ≤ blockU L := H.QL_le_blockU_of_involution hrL hr2 hrQ
  have hxL : x ∉ L := fun hxL => hxV (hQL ⟨hxQ, hxL⟩)
  set ε := x * r with hε
  have hεT : ε ∈ T' := T'.mul_mem (hBT' hxB) (hBT' hrB)
  have hεL : ε ∉ L := by
    intro hεL
    apply hxL
    have : x = ε * r⁻¹ := by rw [hε]; group
    rw [this]
    exact L.mul_mem hεL (L.inv_mem hrL)
  have hzL : z ∈ L := CFSG.CGT.PushingUpLit.blockU_le L hzV
  have hz2 : z * z = 1 := elemAbelian_mul_self H.nat.isElemAbelian_blockU hzV
  have hεz : ε ≠ z := fun h' => hεL (h' ▸ hzL)
  have hzT : z ∈ T' := hQT' (H.blockU_le_QM hzV)
  have hε1 : ε ≠ 1 := fun h' => hεL (h' ▸ L.one_mem)
  have hv1 : h * ε * h⁻¹ ≠ 1 := by
    intro h'
    apply hε1
    have : ε = h⁻¹ * (h * ε * h⁻¹) * h := by group
    rw [this, h']
    group
  obtain ⟨l, hl, hlv⟩ := H.exists_conj_blockU hh hzV hv1 hz1
  set s := l * h with hs'
  have hsε : s * ε * s⁻¹ = z := by
    rw [hs']
    calc l * h * ε * (l * h)⁻¹ = l * (h * ε * h⁻¹) * l⁻¹ := by group
      _ = z := hlv
  set C : Subgroup G := T' ⊓ Subgroup.centralizer ({ε} : Set G) with hC
  set T₁ : Subgroup G := T'.map (MulAut.conj s⁻¹).toMonoidHom with hT₁
  have hεs : ε = s⁻¹ * z * s := by
    rw [← hsε]; group
  have hT₁C : T₁ ≤ Subgroup.centralizer ({ε} : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have h1 := hzc t ht
    calc (s⁻¹ * t * s) * ε = (s⁻¹ * t * s) * (s⁻¹ * z * s) := by rw [← hεs]
      _ = s⁻¹ * (t * z) * s := by group
      _ = s⁻¹ * (z * t) * s := by rw [h1]
      _ = (s⁻¹ * z * s) * (s⁻¹ * t * s) := by group
      _ = ε * (s⁻¹ * t * s) := by rw [← hεs]
  have hT₁syl : CFSG.ABGLocalTools.IsSylowOf 2 T₁ (Subgroup.centralizer ({ε} : Set G)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine CFSG.ABGLocalTools.IsSylowOf.of_le (K := ⊤) ?_ hT₁C le_top
    refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
    rw [hT₁, card_map_conj]
    exact hT'syl.card_eq
  have hC2 : IsPGroup 2 C := hT'syl.isPGroup.to_le inf_le_left
  obtain ⟨c, hcε, hcC⟩ := exists_conj_le_of_isPGroup hT₁syl hC2
    (inf_le_right : C ≤ Subgroup.centralizer ({ε} : Set G))
  set a : G := c⁻¹ * s⁻¹ with ha
  have hcεe : c * ε = ε * c := Subgroup.mem_centralizer_singleton_iff.1 hcε
  have haC : ∀ y ∈ C, a⁻¹ * y * a ∈ T' := by
    intro y hy
    obtain ⟨t, ht, hty⟩ := hcC ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hty
    have : a⁻¹ * y * a = t := by
      rw [ha]
      have h2 : c * y * c⁻¹ = s⁻¹ * t * s := hty.symm
      calc (c⁻¹ * s⁻¹)⁻¹ * y * (c⁻¹ * s⁻¹) = s * (c * y * c⁻¹) * s⁻¹ := by group
        _ = t := by rw [h2]; group
    rw [this]; exact ht
  have haz : a * z * a⁻¹ = ε := by
    rw [ha]
    calc c⁻¹ * s⁻¹ * z * (c⁻¹ * s⁻¹)⁻¹ = c⁻¹ * (s⁻¹ * z * s) * c := by group
      _ = c⁻¹ * ε * c := by rw [← hεs]
      _ = c⁻¹ * (ε * c) := by group
      _ = c⁻¹ * (c * ε) := by rw [← hcεe]
      _ = ε := by group
  have hzCe : z ∈ C := ⟨hzT, Subgroup.mem_centralizer_singleton_iff.2 (hzc ε hεT).symm⟩
  set t₁ : G := a⁻¹ * z * a with ht₁
  have ht₁T : t₁ ∈ T' := haC z hzCe
  have ht₁2 : t₁ * t₁ = 1 := by
    calc t₁ * t₁ = a⁻¹ * (z * z) * a := by rw [ht₁]; group
      _ = 1 := by rw [hz2]; group
  have ht₁1 : t₁ ≠ 1 := by
    intro h'
    apply hz1
    have : z = a * t₁ * a⁻¹ := by rw [ht₁]; group
    rw [this, h']
    group
  have ht₁z : t₁ ≠ z := by
    intro h'
    apply hεz
    have h2 : a⁻¹ * z * a = z := ht₁.symm.trans h'
    calc ε = a * z * a⁻¹ := haz.symm
      _ = a * (a⁻¹ * z * a) * a⁻¹ := by rw [h2]
      _ = z := by group
  set f : G →* G := (MulAut.conj a⁻¹).toMonoidHom with hf
  have hfx : ∀ y : G, f y = a⁻¹ * y * a := by
    intro y
    simp [hf]
  set C₁ : Subgroup G := C.map f with hC₁
  set S₁ : Subgroup G := T' ⊓ Subgroup.centralizer ({t₁} : Set G) with hS₁
  have hC₁S : C₁ ≤ S₁ := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hfx]; exact haC y hy
    · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      rw [hfx]
      have hyz : y * z = z * y := hzc y hy.1
      calc (a⁻¹ * y * a) * t₁ = a⁻¹ * (y * z) * a := by rw [ht₁]; group
        _ = a⁻¹ * (z * y) * a := by rw [hyz]
        _ = t₁ * (a⁻¹ * y * a) := by rw [ht₁]; group
  have ht₁C : t₁ ∈ ⁅C₁, C₁⁆ := by
    have : f z ∈ (⁅C, C⁆).map f := Subgroup.mem_map_of_mem _ hzC
    rw [Subgroup.map_commutator] at this
    rw [hfx] at this
    exact this
  have ht₁S : t₁ ∈ ⁅S₁, S₁⁆ := Subgroup.commutator_mono hC₁S hC₁S ht₁C
  have hA' := hA t₁ ht₁T ht₁2 ht₁1 ht₁z ht₁S
  have hwcases := hA' (a⁻¹ * w * a) (by
    have : f w ∈ (⁅C, C⁆).map f := Subgroup.mem_map_of_mem _ hwC
    rw [Subgroup.map_commutator, hfx] at this
    exact Subgroup.commutator_mono hC₁S hC₁S this)
  have hCT : C ≤ T' := inf_le_left
  have hwL : w ∈ L := hL (Subgroup.commutator_mono hCT hCT hwC)
  have hzε : z * ε = ε * z := (hzc ε hεT).symm ▸ rfl
  rcases hwcases with h1 | h1 | h1 | h1
  · apply hw1
    have : w = a * (a⁻¹ * w * a) * a⁻¹ := by group
    rw [this, h1]; group
  · apply hwz
    have : w = a * (a⁻¹ * w * a) * a⁻¹ := by group
    rw [this, h1, ht₁]
    group
  · apply hεL
    have : w = a * (a⁻¹ * w * a) * a⁻¹ := by group
    have hwe : w = ε := by rw [this, h1, ← haz]
    rw [← hwe]; exact hwL
  · apply hεL
    have : w = a * (a⁻¹ * w * a) * a⁻¹ := by group
    have hwe : w = z * ε := by
      rw [this, h1, ht₁]
      calc a * (a⁻¹ * z * a * z) * a⁻¹ = z * (a * z * a⁻¹) := by group
        _ = z * ε := by rw [haz]
    have : ε = z⁻¹ * w := by rw [hwe]; group
    rw [this]
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    rw [hzinv]
    exact L.mul_mem hzL hwL

end CFSG.CGT.PushingUpLit.T2KR
