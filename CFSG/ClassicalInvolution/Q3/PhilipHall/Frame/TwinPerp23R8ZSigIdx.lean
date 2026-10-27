module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZSigW
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7M1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section PiC

theorem piC_injective_of_eq_bot {Y : Type} [Group Y] {C : Subgroup Y}
    (h : classicalInvolutionOddCore ↥C = ⊥) : Function.Injective (F7I.piC C) :=
  (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk']; exact h)

end PiC

section Odd

theorem odd_index_of_isSylow2In {Y : Type} [Group Y] [Finite Y] {C S₂ : Subgroup Y}
    (hS₂ : IsSylow2In S₂ C) {Q : Type*} [Group Q] (φ : ↥C →* Q) (hφ : Function.Surjective φ)
    {H : Subgroup Q} (hle : ∀ c : ↥C, (c : Y) ∈ S₂ → φ c ∈ H) : Odd H.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle' : S₂.subgroupOf C ≤ H.comap φ := fun c hc =>
    Subgroup.mem_comap.mpr (hle c (Subgroup.mem_subgroupOf.mp hc))
  have hidx : H.index ∣ S₂.relIndex C := by
    rw [← Subgroup.index_comap_of_surjective H hφ]
    exact Subgroup.index_dvd_of_le hle'
  have hnd : ¬ 2 ∣ S₂.relIndex C := by
    obtain ⟨P, hP⟩ := (hS₂.2.1.comap_subtype : IsPGroup 2 (S₂.subgroupOf C)).exists_le_sylow
    have hPm : (P : Subgroup ↥C).map C.subtype = S₂ := by
      refine hS₂.2.2 _ (Subgroup.map_subtype_le _) (P.isPGroup'.map _) fun x hx => ?_
      exact ⟨⟨x, hS₂.1 hx⟩, hP (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    have hPe : (P : Subgroup ↥C) = S₂.subgroupOf C := by
      ext x
      rw [Subgroup.mem_subgroupOf, ← hPm]
      constructor
      · intro hx; exact ⟨x, hx, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        rwa [Subtype.ext hyx] at hy
    have := P.not_dvd_index
    rwa [hPe] at this
  exact Nat.not_even_iff_odd.mp fun h => hnd ((even_iff_two_dvd.mp h).trans hidx)

end Odd

namespace F7K

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.F94
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.F7E
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.F7J

section Index3

variable {Q : Type} [Group Q] [Finite Q]

theorem index_dvd_three {A B : Subgroup Q} {z : Q} (hz : ∀ q : Q, q * z = z * q)
    (hsA : IsUniqueInvolution A z) (hsB : IsUniqueInvolution B z) (h8A : Nat.card A = 8)
    (h8B : Nat.card B = 8)
    (hperm : ∀ q : Q, (conjSub q A = A ∧ conjSub q B = B) ∨ (conjSub q A = B ∧ conjSub q B = A))
    {s : Q} (hsAB : conjSub s A = B) (hsBA : conjSub s B = A) {H : Subgroup Q}
    (hMH : ∀ m : Q, (∀ x ∈ A, m * x = x * m) → (∀ x ∈ B, m * x = x * m) → m ∈ H)
    (hodd : Odd H.index) {ω : Q} (hωH : ω ∈ H) (hωA : conjSub ω A = A) (hωB : conjSub ω B = B)
    (hω3 : ∃ k : ℕ, ω ^ 3 ^ k = 1) (hωmove : ∃ x ∈ A, ω * x ≠ x * ω) : H.index ∣ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N₀ := Subgroup.normalizer (A : Set Q) ⊓ Subgroup.normalizer (B : Set Q) with hN₀
  have hN2 : N₀.index ∣ 2 := by
    refine Subgroup.index_dvd_two_iff.mpr ⟨s, fun b => ?_⟩
    rcases hperm b with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨mem_normalizer_of_conjSub_eq' h1, mem_normalizer_of_conjSub_eq' h2⟩
    · left
      refine ⟨mem_normalizer_of_conjSub_eq' ?_, mem_normalizer_of_conjSub_eq' ?_⟩
      · rw [conjSub_mul, hsAB, h2]
      · rw [conjSub_mul, hsBA, h1]
  let ρ : ↥N₀ →* MulAut ↥A × MulAut ↥B :=
    (A.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_left)).prod
      (B.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_right))
  have hker : ρ.ker ≤ H.subgroupOf N₀ := by
    intro n hn
    rw [MonoidHom.mem_ker, Prod.ext_iff] at hn
    obtain ⟨hnA, hnB⟩ := hn
    refine Subgroup.mem_subgroupOf.mpr (hMH _ (fun x hx => ?_) (fun x hx => ?_))
    · have h1 := congrArg (fun φ : MulAut ↥A => ((φ ⟨x, hx⟩ : ↥A) : Q)) hnA
      simp only [ρ, MonoidHom.prod_apply, MonoidHom.comp_apply, Prod.fst_one,
        Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion,
        MulAut.one_apply] at h1
      exact (comm_of_conj_eq' h1).symm
    · have h1 := congrArg (fun φ : MulAut ↥B => ((φ ⟨x, hx⟩ : ↥B) : Q)) hnB
      simp only [ρ, MonoidHom.prod_apply, MonoidHom.comp_apply, Prod.snd_one,
        Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion,
        MulAut.one_apply] at h1
      exact (comm_of_conj_eq' h1).symm
  obtain ⟨kA, hkA⟩ := card_aut_dvd hz hsA h8A
  obtain ⟨kB, hkB⟩ := card_aut_dvd hz hsB h8B
  have hωN : ω ∈ N₀ := ⟨mem_normalizer_of_conjSub_eq' hωA, mem_normalizer_of_conjSub_eq' hωB⟩
  set ω₀ : ↥N₀ := ⟨ω, hωN⟩ with hω₀
  have hω0H : ω₀ ∈ H.subgroupOf N₀ := hωH
  have hρω : 3 ∣ orderOf (ρ ω₀) := by
    obtain ⟨k, hk⟩ := hω3
    have hp : ρ ω₀ ^ 3 ^ k = 1 := by
      rw [← map_pow]
      have : ω₀ ^ 3 ^ k = 1 := Subtype.ext hk
      rw [this, map_one]
    have h1 : ρ ω₀ ≠ 1 := by
      intro h
      obtain ⟨x, hx, hne⟩ := hωmove
      apply hne
      have h1 := congrArg (fun p : MulAut ↥A × MulAut ↥B => ((p.1 ⟨x, hx⟩ : ↥A) : Q)) h
      simp only [ρ, MonoidHom.prod_apply, MonoidHom.comp_apply,
        Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion,
        Prod.fst_one, MulAut.one_apply] at h1
      exact (comm_of_conj_eq' h1).symm
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hp)
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact h1 (orderOf_eq_one_iff.mp (by simpa using hi))
    rw [hi]
    exact dvd_pow_self 3 hi0
  have h3rel : 3 ∣ ρ.ker.relIndex (H.subgroupOf N₀) := by
    have hk : ρ.ker.subgroupOf (H.subgroupOf N₀) = (ρ.comp (H.subgroupOf N₀).subtype).ker := by
      ext x
      simp [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    rw [Subgroup.relIndex, hk, Subgroup.index_ker]
    have hmem : ρ ω₀ ∈ (ρ.comp (H.subgroupOf N₀).subtype).range := ⟨⟨ω₀, hω0H⟩, rfl⟩
    exact hρω.trans (Subgroup.orderOf_dvd_natCard _ hmem)
  have hindex : ρ.ker.index ∣ 2 ^ kA * 24 * (2 ^ kB * 24) := by
    rw [Subgroup.index_ker]
    refine (Subgroup.card_subgroup_dvd_card _).trans ?_
    rw [Nat.card_prod]
    exact Nat.mul_dvd_mul hkA hkB
  have hrel : 3 * (H.subgroupOf N₀).index ∣ 2 ^ kA * 24 * (2 ^ kB * 24) := by
    refine Dvd.dvd.trans ?_ hindex
    rw [← Subgroup.relIndex_mul_index hker]
    exact Nat.mul_dvd_mul_right h3rel _
  have hH : H.index ∣ (H.subgroupOf N₀).index * N₀.index := by
    have e := Subgroup.relIndex_mul_index (H := H ⊓ N₀) (K := N₀) inf_le_right
    rw [Subgroup.inf_relIndex_right] at e
    change (H.subgroupOf N₀).index * N₀.index = (H ⊓ N₀).index at e
    rw [e]
    exact Subgroup.index_dvd_of_le inf_le_left
  have hall : 3 * H.index ∣ 3 * (3 * 2 ^ (kA + kB + 7)) := by
    have h1 : 3 * H.index ∣ 3 * ((H.subgroupOf N₀).index * N₀.index) := Nat.mul_dvd_mul_left 3 hH
    have h2 : 3 * ((H.subgroupOf N₀).index * N₀.index) ∣
        2 ^ kA * 24 * (2 ^ kB * 24) * 2 := by
      rw [← mul_assoc]
      exact Nat.mul_dvd_mul hrel hN2
    refine h1.trans (h2.trans ?_)
    refine ⟨1, ?_⟩
    rw [pow_add, pow_add]
    ring
  have hall' : H.index ∣ 3 * 2 ^ (kA + kB + 7) := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hall
  exact (Nat.Coprime.pow_right _ (hodd.coprime_two_right)).dvd_of_dvd_mul_right hall'

end Index3

end F7K

section Dvd9

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23_index_centralizer_e_dvd_nine (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hZ : u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y))) :
    ∀ xe : ↥(Subgroup.centralizer ({t} : Set Y)), (xe : Y) = e →
    Odd (Subgroup.centralizer ({F7I.piC (Subgroup.centralizer ({t} : Set Y)) xe} :
        Set (↥(Subgroup.centralizer ({t} : Set Y)) ⧸
          classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y))))).index ∧
      (Subgroup.centralizer ({F7I.piC (Subgroup.centralizer ({t} : Set Y)) xe} :
        Set (↥(Subgroup.centralizer ({t} : Set Y)) ⧸
          classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y))))).index ∣ 9 ∧
      (classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ →
        ∀ ω : Y, ω * t = t * ω → ω * e = e * ω → (∃ k : ℕ, ω ^ 3 ^ k = 1) →
          (∃ k ∈ tightCore R, ω * k ≠ k * ω) →
          (Subgroup.centralizer ({F7I.piC (Subgroup.centralizer ({t} : Set Y)) xe} :
            Set (↥(Subgroup.centralizer ({t} : Set Y)) ⧸
              classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y))))).index ∣ 3) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have hNe := normalizer_le_centralizer_e hd
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hWt : W ≤ C := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw t hd.hzW)
  have htC : t ∈ C := hWt hd.hzW
  have heC : e ∈ C := hWt heW
  have htc : ∀ c ∈ C, c * t = t * c := fun c hc => Subgroup.mem_centralizer_singleton_iff.mp hc
  intro xe hxe
  have hxe' : xe = ⟨e, heC⟩ := Subtype.ext hxe
  subst hxe'
  obtain ⟨qA, qB, h8A, h8B, nA, nB, hcomm, heA, heB, b₁, b', hub, ha, hb, ha1, haz, hb1, hbz⟩ :=
    p23_twin_q8 hc hCdef htC heC
  have hz : ∀ q : ↥C ⧸ classicalInvolutionOddCore ↥C,
      q * F7I.piC C ⟨t, htC⟩ = F7I.piC C ⟨t, htC⟩ * q := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) q
    change F7I.piC C c * _ = _ * F7I.piC C c
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (htc _ c.2))
  have hperm : ∀ q : ↥C ⧸ classicalInvolutionOddCore ↥C,
      (conjSub q (((tightCore R).subgroupOf C).map (F7I.piC C)) =
          ((tightCore R).subgroupOf C).map (F7I.piC C) ∧
        conjSub q ((K'.subgroupOf C).map (F7I.piC C)) = (K'.subgroupOf C).map (F7I.piC C)) ∨
      (conjSub q (((tightCore R).subgroupOf C).map (F7I.piC C)) =
          (K'.subgroupOf C).map (F7I.piC C) ∧
        conjSub q ((K'.subgroupOf C).map (F7I.piC C)) =
          ((tightCore R).subgroupOf C).map (F7I.piC C)) := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) q
    change (conjSub (F7I.piC C c) _ = _ ∧ conjSub (F7I.piC C c) _ = _) ∨
      (conjSub (F7I.piC C c) _ = _ ∧ conjSub (F7I.piC C c) _ = _)
    rw [F7I.conjSub_map_piC, F7I.conjSub_map_piC]
    rcases p23_conj_twins hc c.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [h1, h2]; exact ⟨rfl, rfl⟩
    · right; rw [h1, h2]; exact ⟨rfl, rfl⟩
  obtain ⟨s, hsC, hsN, hsK⟩ := p23_exists_swap hc
  have hsAB : conjSub (F7I.piC C ⟨s, hsC⟩) (((tightCore R).subgroupOf C).map (F7I.piC C)) =
      (K'.subgroupOf C).map (F7I.piC C) := by
    rw [F7I.conjSub_map_piC]
    change ((conjSub s (tightCore R)).subgroupOf C).map _ = _
    rw [hsK]
  have hsBA : conjSub (F7I.piC C ⟨s, hsC⟩) ((K'.subgroupOf C).map (F7I.piC C)) =
      ((tightCore R).subgroupOf C).map (F7I.piC C) := by
    rw [F7I.conjSub_map_piC]
    change ((conjSub s K').subgroupOf C).map _ = _
    rw [p23_swap_conj hc hsC hsK]
  have hMB' := p23MBar_proved hcit hP Y R S t K' W u e g hc hZ ⟨e, heC⟩ rfl
  set H : Subgroup (↥C ⧸ classicalInvolutionOddCore ↥C) :=
    Subgroup.centralizer ({F7I.piC C ⟨e, heC⟩} : Set (↥C ⧸ classicalInvolutionOddCore ↥C)) with hH
  have hMH : ∀ m : ↥C ⧸ classicalInvolutionOddCore ↥C,
      (∀ x ∈ ((tightCore R).subgroupOf C).map (F7I.piC C), m * x = x * m) →
      (∀ x ∈ (K'.subgroupOf C).map (F7I.piC C), m * x = x * m) → m ∈ H := by
    intro m hmA hmB
    rw [hH, Subgroup.mem_centralizer_singleton_iff]
    exact hMB' m hmA hmB
  obtain ⟨S₂, hS₂, hS₂N⟩ := p23_exists_sylow_normW hc
  have hodd : Odd H.index := by
    refine odd_index_of_isSylow2In hS₂ (F7I.piC C) (QuotientGroup.mk'_surjective _) fun c hcS => ?_
    have hcN : (c : Y) ∈ Subgroup.normalizer (W : Set Y) := hS₂N hcS
    have hce : (c : Y) * e = e * c := Subgroup.mem_centralizer_singleton_iff.mp (hNe hcN)
    rw [hH, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hce)
  refine ⟨hodd, F7K.index_dvd_nine hz qA qB h8A h8B hperm hsAB hsBA hMH hodd, ?_⟩
  intro hO ω hωt hωe hω3 hωmove
  have hinj := piC_injective_of_eq_bot hO
  have hωC : ω ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hωt
  have hωK : conjSub ω (tightCore R) = tightCore R := by
    rcases p23_conj_twins hc hωC with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact h1
    · exfalso
      obtain ⟨k, hk⟩ := hω3
      have hsq : conjSub (ω ^ 2) (tightCore R) = tightCore R := by
        rw [pow_two, conjSub_mul, h1, h2]
      have key : ∀ m : ℕ, conjSub (ω ^ (2 * m)) (tightCore R) = tightCore R := by
        intro m
        induction m with
        | zero => simp
        | succ m ih => rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add, conjSub_mul, hsq, ih]
      obtain ⟨r, hr⟩ : Odd (3 ^ k) := Odd.pow (by decide)
      have h3 := key (r + 1)
      rw [show 2 * (r + 1) = 3 ^ k + 1 by omega, pow_succ, hk, one_mul] at h3
      exact hc.std.hne (h1.symm.trans h3)
  have hωB : conjSub ω K' = K' := by
    rcases p23_conj_twins hc hωC with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd (h1.symm.trans hωK) hc.std.hne
  refine F7K.index_dvd_three hz qA qB h8A h8B hperm hsAB hsBA hMH hodd (ω := F7I.piC C ⟨ω, hωC⟩) ?_ ?_ ?_ ?_ ?_
  · rw [hH, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hωe)
  · rw [F7I.conjSub_map_piC]
    change ((conjSub ω (tightCore R)).subgroupOf C).map _ = _
    rw [hωK]
  · rw [F7I.conjSub_map_piC]
    change ((conjSub ω K').subgroupOf C).map _ = _
    rw [hωB]
  · obtain ⟨k, hk⟩ := hω3
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : (⟨ω, hωC⟩ : ↥C) ^ 3 ^ k = 1 := Subtype.ext hk
    rw [this, map_one]
  · obtain ⟨k, hk, hne⟩ := hωmove
    have hkC : k ∈ C := le_centralizer_of_unique (Inner.isUniqueInvolution_core hC.datum) hk
    refine ⟨F7I.piC C ⟨k, hkC⟩, ⟨⟨k, hkC⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩, fun h => hne ?_⟩
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (hinj h)

end Dvd9

section Final

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem ncard_eClass_le_index
    (hO : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥)
    (heC : e ∈ Subgroup.centralizer ({t} : Set Y)) :
    (eClass t e).ncard ≤ (Subgroup.centralizer ({F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨e, heC⟩} :
      Set (↥(Subgroup.centralizer ({t} : Set Y)) ⧸
        classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y))))).index := by
  classical
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hinj := piC_injective_of_eq_bot hO
  set H : Subgroup (↥C ⧸ classicalInvolutionOddCore ↥C) :=
    Subgroup.centralizer ({F7I.piC C ⟨e, heC⟩} : Set (↥C ⧸ classicalInvolutionOddCore ↥C)) with hH
  set H₂ : Subgroup ↥C := H.comap (F7I.piC C) with hH₂
  have hH₂c : ∀ c ∈ H₂, (c : Y) * e = e * c := by
    intro c hc
    rw [hH₂, Subgroup.mem_comap, hH, Subgroup.mem_centralizer_singleton_iff, ← map_mul,
      ← map_mul] at hc
    exact congrArg Subtype.val (hinj hc)
  have hidx : H₂.index = H.index :=
    Subgroup.index_comap_of_surjective H (QuotientGroup.mk'_surjective _)
  let f : ↥C ⧸ H₂ → Y := Quotient.lift (fun c : ↥C => (c : Y) * e * (c : Y)⁻¹) (by
    intro a b hab
    have h := hH₂c _ (QuotientGroup.leftRel_apply.mp hab)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    show (a : Y) * e * (a : Y)⁻¹ = (b : Y) * e * (b : Y)⁻¹
    calc (a : Y) * e * (a : Y)⁻¹ = (a : Y) * (e * ((a : Y)⁻¹ * b)) * (b : Y)⁻¹ := by group
      _ = (a : Y) * (((a : Y)⁻¹ * b) * e) * (b : Y)⁻¹ := by rw [h]
      _ = (b : Y) * e * (b : Y)⁻¹ := by group)
  have hrange : eClass t e ⊆ Set.range f := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨QuotientGroup.mk (⟨c, hc⟩ : ↥C), rfl⟩
  calc (eClass t e).ncard ≤ (Set.range f).ncard := Set.ncard_le_ncard hrange (Set.toFinite _)
    _ ≤ Nat.card (↥C ⧸ H₂) := by
      rw [← Set.image_univ, ← Set.ncard_univ (↥C ⧸ H₂)]
      exact Set.ncard_image_le (Set.toFinite _)
    _ = H.index := hidx

theorem p23_eClass_ncard_le_three (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hZ : u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)))
    (hO : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥)
    {ω : Y} (hωt : ω * t = t * ω) (hωe : ω * e = e * ω) (hω3 : IsPGroup 3 (Subgroup.zpowers ω))
    (hωmove : ∃ k ∈ tightCore R, ω * k ≠ k * ω) :
    (eClass t e).ncard ≤ 3 := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have heC : e ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab e heW t hd.hzW)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ω ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hω3 ⟨ω, Subgroup.mem_zpowers ω⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨-, -, h3⟩ := p23_index_centralizer_e_dvd_nine hcit hP hc hZ ⟨e, heC⟩ rfl
  have hle := Nat.le_of_dvd (by norm_num) (h3 hO ω hωt hωe ⟨k, hk⟩ hωmove)
  exact (ncard_eClass_le_index hO heC).trans hle

end Final

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
