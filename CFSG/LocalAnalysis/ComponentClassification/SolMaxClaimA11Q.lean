module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA11P
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36J

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped Pointwise

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {S : Sig36 X t J n e E D} {e₀ s : X} {k : ℕ} {L₀ F N : Subgroup X} {r : ℕ}
  {θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin r)}
  {ρN : ↥(normalizer (N : Set X)) →* Perm (Fin r)} {τ' : Perm (Fin r)} {DN : Finset (Fin r)}

namespace PumpG

variable (P : S.PumpG e₀ s k L₀ F N r θN ρN τ' DN)
include P

theorem F_le_normalizer_coreN : F ≤ normalizer (coreNOf N : Set X) := fun _x hx =>
  le_normalizer_pPrimeCore (P.L₀NN (P.FL₀ hx))

theorem isPGroup_F : IsPGroup 2 F :=
  IsPGroup.of_card (n := 2) (by rw [P.F4]; norm_num)

theorem mem_coreN_of_rho_of_le (hr : 4 ≤ r) {z : X} (hzN : z ∈ N)
    (hz : ρN ⟨z, le_normalizer hzN⟩ = 1) : z ∈ coreNOf N := by
  have h1 := P.perm.apply_of_mem hr ⟨z, hzN⟩
  rw [hz] at h1
  have h2 : θN ((⟨z, hzN⟩ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) = 1 := Subtype.ext h1.symm
  rw [← map_one θN] at h2
  have h3 := θN.injective h2
  rw [QuotientGroup.eq_one_iff] at h3
  exact ⟨_, h3, rfl⟩

theorem mem_of_normalizes {H : Subgroup X} (hFH : normalizer (F : Set X) ≤ H) (hFH' : F ≤ H)
    (hOH : coreNOf N ≤ H) {x : X}
    (hx : ∀ f ∈ F, ∃ f' ∈ F, x * f * x⁻¹ * f'⁻¹ ∈ coreNOf N) : x ∈ H := by
  have hle : F.map (MulAut.conj x).toMonoidHom ≤ F ⊔ coreNOf N := by
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨f', hf', hff'⟩ := hx f hf
    have h1 : (MulAut.conj x).toMonoidHom f = (x * f * x⁻¹ * f'⁻¹) * f' := by
      change x * f * x⁻¹ = _
      group
    rw [h1]
    exact mul_mem (mem_sup_right hff') (mem_sup_left hf')
  have hcard : Nat.card (F.map (MulAut.conj x).toMonoidHom) = Nat.card F :=
    card_map_of_injective (MulAut.conj x).injective
  obtain ⟨c, hc, hcF⟩ := exists_conj_of_le_sup_odd' P.F_le_normalizer_coreN P.isPGroup_F
    (odd_coreNOf N) hle hcard
  have hcH : c ∈ H := (sup_le hFH' hOH) hc
  have hcx : c * x ∈ normalizer (F : Set X) := by
    rw [mem_normalizer_iff_map_conj_eq]
    calc F.map (MulAut.conj (c * x)).toMonoidHom =
        (F.map (MulAut.conj x).toMonoidHom).map (MulAut.conj c).toMonoidHom := by
          rw [Subgroup.map_map]
          congr 1
          ext z
          simp [MulAut.conj_apply, mul_assoc]
      _ = F := hcF
  have h1 := mul_mem (inv_mem hcH) (hFH hcx)
  rwa [inv_mul_cancel_left] at h1

theorem le_of_seven_le (hk : 7 ≤ k) (hr8 : r ≠ 8) {H : Subgroup X}
    (hFH : normalizer (F : Set X) ≤ H) (hL₀H : L₀ ≤ H) (hOH : coreNOf N ≤ H) : N ≤ H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr7 : 7 ≤ r := hk.trans P.kr
  set π : ↥N →* alternatingGroup (Fin r) :=
    θN.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥N)) with hπdef
  have hπs : Function.Surjective π := θN.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπρ : ∀ x : ↥N, ((π x : alternatingGroup (Fin r)) : Perm (Fin r)) =
      ρN ⟨x, le_normalizer x.2⟩ := fun x => (P.perm.apply_of_mem (by omega) x).symm
  have hπker : ∀ x : ↥N, π x = 1 → (x : X) ∈ coreNOf N := by
    intro x hx
    refine P.mem_coreN_of_rho_of_le (by omega) x.2 ?_
    rw [← hπρ, hx]
    rfl
  have hFH' : F ≤ H := P.FL₀.trans hL₀H
  set Y := H.subgroupOf N with hYdef
  suffices hY : Y.map π = ⊤ by
    intro x hx
    obtain ⟨y, hy, hyx⟩ : π ⟨x, hx⟩ ∈ Y.map π := by rw [hY]; exact mem_top _
    have h1 : π (y⁻¹ * ⟨x, hx⟩) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
    have h2 := mul_mem (show (y : X) ∈ H from hy) (hOH (hπker _ h1))
    simpa using h2
  obtain ⟨f₀, hf₀F, hf₀1⟩ : ∃ f₀ ∈ F, f₀ ≠ 1 := by
    rcases F.bot_or_exists_ne_one with h | h
    · have h4 := P.F4
      rw [h, Subgroup.card_bot] at h4
      exact absurd h4 (by norm_num)
    · exact h
  obtain ⟨ψ, hψ⟩ := P.iso
  by_cases hfix : N.map (MulAut.conj s).toMonoidHom = N
  ·
    have hL₀N : L₀ ≤ N := by
      have h1 := P.L₀N
      rwa [hfix, sup_idem] at h1
    have hFN : F ≤ N := P.FL₀.trans hL₀N
    set V := (F.subgroupOf N).map π with hVdef
    have hFO : F.subgroupOf N ⊓ π.ker = ⊥ := by
      have h1 : π.ker = pPrimeCore 2 ↥N := by
        ext x
        rw [MonoidHom.mem_ker]
        change θN (QuotientGroup.mk' (pPrimeCore 2 ↥N) x) = 1 ↔ _
        rw [map_eq_one_iff _ θN.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      rw [h1]
      refine inf_eq_bot_of_two_odd ?_ ?_
      · exact P.isPGroup_F.of_equiv (subgroupOfEquivOfLe hFN).symm
      · exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have hV4 : Nat.card V = 4 := by
      rw [hVdef, card_map_of_inf_ker π _ hFO, Nat.card_congr (subgroupOfEquivOfLe hFN).toEquiv,
        P.F4]
    have hV2 : ∀ v ∈ V, v ^ 2 = 1 := by
      rintro _ ⟨f, hf, rfl⟩
      rw [← map_pow, sq, show f * f = 1 from Subtype.ext (P.Fsq f hf), map_one]
    have hVs : ∀ v ∈ V, ∀ ω ∉ DN, (v : Perm (Fin r)) ω = ω := by
      rintro _ ⟨f, hf, rfl⟩ ω hω
      rw [hπρ]
      exact P.Fsupp f hf ω hω
    have hstab := Sol78.stabilizer_le_normalizer_of_support P.DN4 hV4 hV2 hVs
    have hSY : MulAction.stabilizer (alternatingGroup (Fin r)) (DN : Set (Fin r)) ≤ Y.map π := by
      intro b hb
      obtain ⟨x, rfl⟩ := hπs b
      refine ⟨x, ?_, rfl⟩
      change (x : X) ∈ H
      refine P.mem_of_normalizes hFH hFH' hOH fun f hf => ?_
      have hfN : f ∈ N := hFN hf
      have h1 := (mem_normalizer_iff.mp (hstab hb) (π ⟨f, hfN⟩)).mp ⟨⟨f, hfN⟩, hf, rfl⟩
      obtain ⟨⟨f', hf'N⟩, hf', hff'⟩ := h1
      refine ⟨f', hf', ?_⟩
      have hz : (x : X) * f * (x : X)⁻¹ * f'⁻¹ =
          ((x * ⟨f, hfN⟩ * x⁻¹ * (⟨f', hf'N⟩ : ↥N)⁻¹ : ↥N) : X) := rfl
      rw [hz]
      refine hπker _ ?_
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hff', mul_inv_cancel]
    have hcF : 7 ≤ (τ'.supportᶜ).card := by
      rw [Finset.card_compl, Fintype.card_fin]
      have := P.τk
      omega
    obtain ⟨d, hd⟩ := Finset.card_pos.mp (by rw [P.DN4]; norm_num : 0 < DN.card)
    obtain ⟨u, hu, hun⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := DN) (t := τ'.supportᶜ) (by rw [P.DN4]; omega)
    obtain ⟨v, hv, hvn⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := insert u DN) (t := τ'.supportᶜ)
      (lt_of_le_of_lt (Finset.card_insert_le _ _) (by rw [P.DN4]; omega))
    rw [Finset.mem_insert, not_or] at hvn
    have hdu : d ≠ u := fun h => hun (h ▸ hd)
    have hdv : d ≠ v := fun h => hvn.2 (h ▸ hd)
    have huv : u ≠ v := Ne.symm hvn.1
    have hdF : d ∈ τ'.supportᶜ := P.DNfix hd
    set b₀ : alternatingGroup (Fin r) := ⟨swap d u * swap d v, by
      rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hdu, Perm.sign_swap hdv]
      decide⟩ with hb₀
    have hb₀F : b₀ ∈ fixAlt τ' := by
      rw [mem_fixAlt]
      intro z hz
      have hz' : (swap d u * swap d v) z ≠ z := Perm.mem_support.mp hz
      by_contra hzF
      apply hz'
      have hzd : z ≠ d := fun h => hzF (h ▸ hdF)
      have hzu : z ≠ u := fun h => hzF (h ▸ hu)
      have hzv : z ≠ v := fun h => hzF (h ▸ hv)
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hzd hzv, swap_apply_of_ne_of_ne hzd hzu]
    have hb₀S : b₀ ∉ MulAction.stabilizer (alternatingGroup (Fin r)) (DN : Set (Fin r)) := by
      intro h
      have h1 := (Sol78.apply_mem_iff_of_mem_stabilizer h d).mpr hd
      change (swap d u * swap d v) d ∈ DN at h1
      rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hdv) (Ne.symm huv)]
        at h1
      exact hvn.2 h1
    have hb₀Y : b₀ ∈ Y.map π := by
      obtain ⟨q, hq⟩ := ψ.surjective ⟨b₀, hb₀F⟩
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      have hlN : (l : X) ∈ N := hL₀N l.2
      refine ⟨⟨l, hlN⟩, hL₀H l.2, Subtype.ext ?_⟩
      rw [hπρ]
      have h1 := hψ l
      rw [hq] at h1
      exact h1.symm
    have hco := alternatingGroup.isCoatom_stabilizer (α := Fin r) (s := (DN : Set (Fin r)))
      (Finset.coe_nonempty.mpr ⟨d, hd⟩) ⟨u, hun⟩
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin, Set.ncard_coe_finset, P.DN4]; omega)
    exact hco.2 _ (lt_of_le_of_ne hSY fun h => hb₀S (h ▸ hb₀Y))
  ·
    have hrk : r = k := by
      rcases P.case with h | ⟨h, -⟩
      · exact h
      · exact absurd h hfix
    have hτ0 : τ'.support = ∅ := by
      have h1 := P.τk
      have h2 : τ'.support.card ≤ r := by
        have := Finset.card_le_univ τ'.support
        rwa [Fintype.card_fin] at this
      rw [← Finset.card_eq_zero]
      omega
    have hall : ∀ b : alternatingGroup (Fin r), b ∈ fixAlt τ' := by
      intro b
      rw [mem_fixAlt, hτ0, Finset.compl_empty]
      exact Finset.subset_univ _
    have hlift : ∀ b : alternatingGroup (Fin r), ∃ l : ↥L₀,
        ρN ⟨l, P.L₀NN l.2⟩ = (b : Perm (Fin r)) := by
      intro b
      obtain ⟨q, hq⟩ := ψ.surjective ⟨b, hall b⟩
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      refine ⟨l, ?_⟩
      rw [← hψ l, hq]
    have hnorm : (Y.map π).Normal := ⟨fun z hz b => by
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨l, hl⟩ := hlift b
      have hlyN : (l : X) * y * (l : X)⁻¹ ∈ N :=
        (mem_normalizer_iff.mp (P.L₀NN l.2) y).mp y.2
      refine ⟨⟨_, hlyN⟩, ?_, ?_⟩
      · change (l : X) * y * (l : X)⁻¹ ∈ H
        exact mul_mem (mul_mem (hL₀H l.2) hy) (inv_mem (hL₀H l.2))
      · apply Subtype.ext
        have h1 := P.perm ⟨l, P.L₀NN l.2⟩ y
        have h2 : (N.normalizerMonoidHom ⟨l, P.L₀NN l.2⟩ y : ↥N) = ⟨_, hlyN⟩ :=
          Subtype.ext rfl
        rw [h2, hl] at h1
        exact h1⟩
    have hρf₀ : ρN ⟨f₀, P.L₀NN (P.FL₀ hf₀F)⟩ ∈ alternatingGroup (Fin r) := by
      rw [← hψ ⟨f₀, P.FL₀ hf₀F⟩]
      exact (ψ _).1.2
    have hρf₀1 : ρN ⟨f₀, P.L₀NN (P.FL₀ hf₀F)⟩ ≠ 1 := by
      intro h
      rw [← hψ ⟨f₀, P.FL₀ hf₀F⟩] at h
      have h1 : ψ ((⟨f₀, P.FL₀ hf₀F⟩ : ↥L₀) : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) = 1 :=
        Subtype.ext (Subtype.ext h)
      rw [← map_one ψ] at h1
      have h2 := ψ.injective h1
      rw [QuotientGroup.eq_one_iff] at h2
      have hodd : Odd (orderOf f₀) := by
        have h3 := orderOf_dvd_natCard (⟨⟨f₀, P.FL₀ hf₀F⟩, h2⟩ : ↥(pPrimeCore 2 ↥L₀))
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h3
        exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right h3 pPrimeCore_coprime_card)
      have h4 : orderOf f₀ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact P.Fsq f₀ hf₀F)
      rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h5 | h5
      · exact hf₀1 (orderOf_eq_one_iff.mp h5)
      · rw [h5] at hodd
        exact absurd hodd (by decide)
    obtain ⟨x, hx⟩ := hπs ⟨_, hρf₀⟩
    have hxH : (x : X) ∈ H := by
      refine P.mem_of_normalizes hFH hFH' hOH fun f hf => ⟨f, hf, ?_⟩
      have hfN : f ∈ normalizer (N : Set X) := P.L₀NN (P.FL₀ hf)
      have hcN : (x : X) * f * (x : X)⁻¹ * f⁻¹ ∈ N := by
        have h1 : f * (x : X)⁻¹ * f⁻¹ ∈ N := (mem_normalizer_iff.mp hfN _).mp (inv_mem x.2)
        have h2 := mul_mem x.2 h1
        simpa [mul_assoc] using h2
      refine P.mem_coreN_of_rho_of_le (by omega) hcN ?_
      have h1 : (⟨(x : X) * f * (x : X)⁻¹ * f⁻¹, le_normalizer hcN⟩ :
          ↥(normalizer (N : Set X))) = ⟨x, le_normalizer x.2⟩ * ⟨f, hfN⟩ *
            (⟨x, le_normalizer x.2⟩)⁻¹ * (⟨f, hfN⟩)⁻¹ := rfl
      have hxρ : ρN ⟨x, le_normalizer x.2⟩ = ρN ⟨f₀, P.L₀NN (P.FL₀ hf₀F)⟩ := by
        rw [← hπρ, hx]
      have hcomm : ρN ⟨f₀, P.L₀NN (P.FL₀ hf₀F)⟩ * ρN ⟨f, hfN⟩ =
          ρN ⟨f, hfN⟩ * ρN ⟨f₀, P.L₀NN (P.FL₀ hf₀F)⟩ := by
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        change f₀ * f = f * f₀
        have hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := by
          intro a ha b hb
          have hk4 := klein_of_card_sq P.F4 P.Fsq
          exact congrArg Subtype.val
            ((isElementaryAbelian_of_klein hk4).toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
        exact hFab f₀ hf₀F f hf
      rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv, hxρ, hcomm]
      group
    have hY1 : Y.map π ≠ ⊥ := by
      intro h
      have h1 : π x ∈ Y.map π := ⟨x, hxH, rfl⟩
      rw [h, mem_bot, hx] at h1
      exact hρf₀1 (congrArg Subtype.val h1)
    have : IsSimpleGroup (alternatingGroup (Fin r)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Y.map π)).resolve_left hY1

theorem le (hk : 9 ≤ k) {H : Subgroup X} (hFH : normalizer (F : Set X) ≤ H) (hL₀H : L₀ ≤ H)
    (hOH : coreNOf N ≤ H) : N ≤ H :=
  P.le_of_seven_le (by omega) (by have := P.kr; omega) hFH hL₀H hOH

end PumpG

end Sig36

end CFSG.ComponentClassification.SolMax
