module

public import CFSG.GroupTheory.SylowPQMaximal.Defs
import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow

public section

namespace CFSG.GroupTheory

open Subgroup

variable {p q : ℕ} {Y : Type*} [Group Y]

theorem exists_sylow_le_subgroupOf_of_normal [Finite Y] [Fact p.Prime] (N : Subgroup Y)
    [N.Normal] (P : Sylow p Y) {H : Subgroup Y} (hPH : (P : Subgroup Y) ≤ H) :
    ∃ Q : Sylow p N, (Q : Subgroup N) ≤ H.subgroupOf N := by
  obtain ⟨Q, hQ⟩ := CFSG.QuasithinUnique.exists_sylow_eq_subgroupOf_of_normal P N
  refine ⟨Q, ?_⟩
  rw [hQ]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact hPH hx

theorem exists_sylow_le_map_of_surjective [Finite Y] [Fact p.Prime] {Y' : Type*} [Group Y']
    {f : Y →* Y'} (hf : Function.Surjective f) (P : Sylow p Y) {H : Subgroup Y}
    (hPH : (P : Subgroup Y) ≤ H) : ∃ Q : Sylow p Y', (Q : Subgroup Y') ≤ H.map f := by
  refine ⟨P.mapSurjective hf, ?_⟩
  rw [Sylow.coe_mapSurjective]
  exact Subgroup.map_mono hPH

theorem SylowPQMaximal.of_surjective [Finite Y] [Fact p.Prime] {Y' : Type*} [Group Y']
    (f : Y →* Y') (hf : Function.Surjective f) (hK : SylowPQMaximal p q f.ker)
    (hY' : SylowPQMaximal p q Y') : SylowPQMaximal p q Y := by
  intro P H hPH hH
  have hcardSub : Nat.card ↥(H.subgroupOf f.ker) = Nat.card ↥(f.ker ⊓ H) := by
    rw [← Subgroup.card_map_of_injective (K := H.subgroupOf f.ker) (f := (f.ker).subtype)
      (f.ker).subtype_injective, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hcardSub' : Nat.card ↥((f.ker).subgroupOf H) = Nat.card ↥(f.ker ⊓ H) := by
    rw [← Subgroup.card_map_of_injective (K := (f.ker).subgroupOf H) (f := H.subtype)
      H.subtype_injective, Subgroup.subgroupOf_map_subtype]
  have hpiK : IsPiSubgroup {r : Nat.Primes | (r : ℕ) = p ∨ (r : ℕ) = q} (H.subgroupOf f.ker) := by
    have hdiv : Nat.card ↥(H.subgroupOf f.ker) ∣ Nat.card ↥H := by
      rw [hcardSub]
      exact Subgroup.card_dvd_of_le inf_le_right
    intro r hr
    exact hH r (hr.trans hdiv)
  have hpiMap : IsPiSubgroup {r : Nat.Primes | (r : ℕ) = p ∨ (r : ℕ) = q} (H.map f) := by
    intro r hr
    exact hH r (hr.trans (Subgroup.card_map_dvd H f))
  obtain ⟨Q, hQ⟩ := exists_sylow_le_subgroupOf_of_normal f.ker P hPH
  have hHKer : IsPGroup p ↥(H.subgroupOf f.ker) := hK Q _ hQ hpiK
  obtain ⟨Q', hQ'⟩ := exists_sylow_le_map_of_surjective hf P hPH
  have hImg : IsPGroup p ↥(H.map f) := hY' Q' _ hQ' hpiMap
  have hkerp : IsPGroup p ↥((f.ker).subgroupOf H) := by
    obtain ⟨a, ha⟩ := hHKer.exists_card_eq
    exact IsPGroup.of_card (n := a) (hcardSub'.trans (hcardSub.symm.trans ha))
  have hkereq : (f.comp H.subtype).ker = (f.ker).subgroupOf H :=
    (MonoidHom.comap_ker f H.subtype).symm
  have hkerp' : IsPGroup p ↥(f.comp H.subtype).ker := by
    rw [hkereq]
    exact hkerp
  have hcomap : Subgroup.comap (f.comp H.subtype) (H.map f) = ⊤ := by
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_top, iff_true]
    exact ⟨x, x.2, rfl⟩
  have hHcomp : IsPGroup p ↥(Subgroup.comap (f.comp H.subtype) (H.map f)) :=
    hImg.comap_of_ker_isPGroup (f.comp H.subtype) hkerp'
  rw [hcomap] at hHcomp
  exact hHcomp.of_equiv Subgroup.topEquiv

theorem SylowPQMaximal.of_normal [Finite Y] [Fact p.Prime] (N : Subgroup Y) [N.Normal]
    (hN : SylowPQMaximal p q N) (hQ : SylowPQMaximal p q (Y ⧸ N)) : SylowPQMaximal p q Y := by
  have e : ↥N ≃* ↥(QuotientGroup.mk' N).ker :=
    MulEquiv.subgroupCongr (QuotientGroup.ker_mk' N).symm
  have hK : SylowPQMaximal p q (QuotientGroup.mk' N).ker :=
    SylowPQMaximal.of_mulEquiv e hN
  exact SylowPQMaximal.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hK hQ

theorem SylowPQMaximal.of_normal_of_isPGroup_quotient [Finite Y] [Fact p.Prime] (N : Subgroup Y)
    [N.Normal] (hN : SylowPQMaximal p q N) (hQ : IsPGroup p (Y ⧸ N)) : SylowPQMaximal p q Y :=
  SylowPQMaximal.of_normal N hN (SylowPQMaximal.of_isPGroup hQ)

theorem SylowPQMaximal.of_quotient_of_isPGroup [Finite Y] [Fact p.Prime] (N : Subgroup Y)
    [N.Normal] (hN : IsPGroup p N) (hQ : SylowPQMaximal p q (Y ⧸ N)) :
    SylowPQMaximal p q Y :=
  SylowPQMaximal.of_normal N (SylowPQMaximal.of_isPGroup hN) hQ

theorem SylowPQMaximal.quotient_of_isPGroup [Finite Y] [Fact p.Prime] (N : Subgroup Y)
    [N.Normal] (hN : IsPGroup p N) (h : SylowPQMaximal p q Y) :
    SylowPQMaximal p q (Y ⧸ N) := by
  intro Pbar Hbar hPH hH
  let π := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hNp : IsPGroup p ↥π.ker := by
    rw [hker]
    exact hN
  let P₁ : Subgroup Y := (Pbar : Subgroup (Y ⧸ N)).comap π
  have hP₁p : IsPGroup p ↥P₁ := Pbar.isPGroup'.comap_of_ker_isPGroup π hNp
  have hidx : ¬ p ∣ P₁.index := by
    rw [show P₁.index = (Pbar : Subgroup (Y ⧸ N)).index from
      Subgroup.index_comap_of_surjective (H := (Pbar : Subgroup (Y ⧸ N))) hπ]
    exact Sylow.not_dvd_index Pbar
  let P : Sylow p Y := hP₁p.toSylow hidx
  have hPcoe : (P : Subgroup Y) = P₁ := IsPGroup.toSylow_coe hP₁p hidx
  have hPH' : (P : Subgroup Y) ≤ Hbar.comap π := by
    rw [hPcoe]
    exact Subgroup.comap_mono hPH
  have hcard : Nat.card ↥(Hbar.comap π) = Nat.card ↥Hbar * Nat.card ↥N := by
    have hNP : N ≤ Hbar.comap π := fun x hx => by
      have h1 : (x : Y ⧸ N) = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      show (x : Y ⧸ N) ∈ Hbar
      rw [h1]
      exact one_mem _
    have h1 := Subgroup.card_ker_mul_card_range (π.comp (Hbar.comap π).subtype)
    have hker' : (π.comp (Hbar.comap π).subtype).ker = N.subgroupOf (Hbar.comap π) := by
      ext x
      simp [π, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hrange' : (π.comp (Hbar.comap π).subtype).range = Hbar := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype,
        Subgroup.map_comap_eq_self_of_surjective hπ]
    rw [hker', hrange', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv] at h1
    exact h1.symm.trans (Nat.mul_comm _ _)
  have hpiH : IsPiSubgroup {r : Nat.Primes | (r : ℕ) = p ∨ (r : ℕ) = q} (Hbar.comap π) := by
    intro r hr
    have hr' : (r : ℕ) ∣ Nat.card ↥Hbar * Nat.card ↥N := by
      rw [← hcard]
      exact hr
    rcases (Nat.Prime.dvd_mul r.2).mp hr' with h1 | h1
    · exact hH r h1
    · obtain ⟨n, hn⟩ := hN.exists_card_eq
      have hdvd : (r : ℕ) ∣ p := Nat.Prime.dvd_of_dvd_pow r.2 (hn ▸ h1)
      rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h2 | h2
      · exact absurd h2 (Nat.Prime.ne_one r.2)
      · exact Or.inl h2
  have hHp : IsPGroup p ↥(Hbar.comap π) := h P (Hbar.comap π) hPH' hpiH
  have hmapH : (Hbar.comap π).map π = Hbar :=
    Subgroup.map_comap_eq_self_of_surjective hπ Hbar
  have hres := hHp.map π
  rw [hmapH] at hres
  exact hres

theorem SylowPQMaximal.prod [Fact p.Prime] {A B : Type*} [Group A] [Group B] [Finite A]
    [Finite B] (hA : SylowPQMaximal p q A) (hB : SylowPQMaximal p q B) :
    SylowPQMaximal p q (A × B) := by
  have hf : Function.Surjective (MonoidHom.snd A B) := fun b => ⟨(1, b), rfl⟩
  have hker : SylowPQMaximal p q (MonoidHom.snd A B).ker := by
    have hrange : (MonoidHom.inl A B).range = (MonoidHom.snd A B).ker := by
      ext x
      simp only [MonoidHom.mem_range, MonoidHom.mem_ker]
      constructor
      · rintro ⟨a, rfl⟩
        rfl
      · intro hx
        refine ⟨x.1, ?_⟩
        ext
        · rfl
        · simpa using hx.symm
    let e₁ : A ≃* ↥(MonoidHom.inl A B).range :=
      MonoidHom.ofInjective (f := MonoidHom.inl A B) (by
        intro a b hab
        simpa using hab)
    have e₂ : ↥(MonoidHom.inl A B).range ≃* ↥(MonoidHom.snd A B).ker :=
      MulEquiv.subgroupCongr hrange
    exact SylowPQMaximal.of_mulEquiv (e₁.trans e₂) hA
  exact SylowPQMaximal.of_surjective (MonoidHom.snd A B) hf hker hB

end CFSG.GroupTheory
