module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.A5

theorem conj_mem_Q {G : Type} [Group G] {L Q : Subgroup G} (hQL : Q ≤ L) (hQ2 : IsPGroup 2 ↥Q)
    (α : ↥L →* ↥(alternatingGroup (Fin 5))) (hα : Function.Surjective α)
    (hαQ : ∀ l : ↥L, α l = 1 ↔ (l : G) ∈ Q) {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    {q : G} (hq : q ∈ Q) : g * q * g⁻¹ ∈ Q := by
  classical
  have hconjL : ∀ (y : G), y ∈ Subgroup.normalizer (L : Set G) → ∀ x : G, x ∈ L →
      y * x * y⁻¹ ∈ L := fun y hy x hx => (Subgroup.mem_normalizer_iff.1 hy x).1 hx
  have hQn : ∀ (l : ↥L) (x : G), x ∈ Q → (l : G) * x * (l : G)⁻¹ ∈ Q := by
    intro l x hx
    have hxL : x ∈ L := hQL hx
    have h1 : α ⟨x, hxL⟩ = 1 := (hαQ ⟨x, hxL⟩).2 hx
    have h2 : α (l * ⟨x, hxL⟩ * l⁻¹) = 1 := by rw [map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel]
    exact (hαQ _).1 h2
  have hginv : g⁻¹ ∈ Subgroup.normalizer (L : Set G) := inv_mem hg
  let c : ↥Q →* ↥L := MonoidHom.mk' (fun q : ↥Q => (⟨g * q * g⁻¹, hconjL g hg q (hQL q.2)⟩ : ↥L))
    (fun a b => by
      apply Subtype.ext
      simp [mul_assoc])
  let φ : ↥Q →* ↥(alternatingGroup (Fin 5)) := α.comp c
  have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hHn : φ.range.Normal := by
    refine ⟨fun n hn a => ?_⟩
    obtain ⟨q', rfl⟩ := hn
    obtain ⟨l, rfl⟩ := hα a
    let l' : ↥L := ⟨g⁻¹ * (l : G) * g, hconjL g⁻¹ hginv l l.2 |> fun h => by
      simpa [mul_assoc] using h⟩
    have hq'' : (l' : G) * (q' : G) * (l' : G)⁻¹ ∈ Q := hQn l' q' q'.2
    refine ⟨⟨(l' : G) * (q' : G) * (l' : G)⁻¹, hq''⟩, ?_⟩
    show α (c ⟨_, hq''⟩) = α l * α (c q') * (α l)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [c, MonoidHom.mk'_apply, Subgroup.coe_mul, InvMemClass.coe_inv, l']
    group
  have hH2 : IsPGroup 2 φ.range := hQ2.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hHbot : φ.range = ⊥ := by
    rcases hHn.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      rw [h] at hH2
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hH2.of_equiv Subgroup.topEquiv)
      rw [Delta5.a5_card] at hn
      have h3 : 3 ∣ 2 ^ n := (show (60 : ℕ) = 2 ^ n from hn) ▸ (by norm_num : 3 ∣ 60)
      have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h3
      omega
  have hφ1 : φ ⟨q, hq⟩ = 1 := by
    have : φ ⟨q, hq⟩ ∈ φ.range := ⟨⟨q, hq⟩, rfl⟩
    rw [hHbot, Subgroup.mem_bot] at this
    exact this
  exact (hαQ (c ⟨q, hq⟩)).1 hφ1

theorem normalizer_le_normalizer_Q {G : Type} [Group G] {L Q : Subgroup G} (hQL : Q ≤ L)
    (hQ2 : IsPGroup 2 ↥Q) (α : ↥L →* ↥(alternatingGroup (Fin 5))) (hα : Function.Surjective α)
    (hαQ : ∀ l : ↥L, α l = 1 ↔ (l : G) ∈ Q) {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) : g ∈ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    exact conj_mem_Q hQL hQ2 α hα hαQ hg hq
  · intro h
    have h1 := conj_mem_Q hQL hQ2 α hα hαQ (inv_mem hg) h
    have e : g⁻¹ * (g * q * g⁻¹) * g⁻¹⁻¹ = q := by group
    rwa [e] at h1

end CFSG.QuasithinUnique.A5
