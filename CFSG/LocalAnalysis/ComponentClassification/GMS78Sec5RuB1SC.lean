module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type*} [Group G]

private theorem exists_isSylowOf_two_le {P K : Subgroup G} (hP : IsPGroup 2 P) (hPK : P ≤ K) :
    ∃ Q : Subgroup G, IsSylowOf 2 Q K ∧ P ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, fun t ht => ?_⟩
  exact ⟨⟨t, hPK ht⟩, hQ (show (⟨t, hPK ht⟩ : K) ∈ P.subgroupOf K from ht), rfl⟩

private theorem exists_conj_le_of_isSylowOf [Finite G] {S K Q : Subgroup G}
    (hS : IsSylowOf 2 S K) (hQK : Q ≤ K) (hQ : IsPGroup 2 Q) :
    ∃ k ∈ K, ∀ x ∈ Q, k⁻¹ * x * k ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, ⟨P', rfl⟩, hQP⟩ := exists_isSylowOf_two_le hQ hQK
  obtain ⟨S', rfl⟩ := hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S' P'
  refine ⟨g, g.2, fun x hx => ?_⟩
  obtain ⟨z, hz, rfl⟩ := hQP hx
  have hz' : z ∈ MulAut.conj g • (S' : Subgroup K) := by
    change z ∈ ((g • S' : Sylow 2 K) : Subgroup K)
    rw [hg]
    exact hz
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply] at hz'
  exact ⟨_, hz', rfl⟩

private theorem conj_mul_self_eq_one (h x : G) (hx : x * x = 1) :
    (h⁻¹ * x * h) * (h⁻¹ * x * h) = 1 := by
  calc (h⁻¹ * x * h) * (h⁻¹ * x * h) = h⁻¹ * (x * x) * h := by group
    _ = 1 := by rw [hx, mul_one, inv_mul_cancel]

theorem stronglyClosed_of_conj_control [Finite G] {K S A X N : Subgroup G}
    (hS : IsSylowOf 2 S K) (hAS : A ≤ S) (hAX : A ≤ centralizer (X : Set G))
    (hX2 : ∀ x ∈ X, x * x = 1)
    (hα : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ S → g ∈ N)
    (hF4 : ∀ n ∈ N ⊓ K, ∀ x ∈ X, n⁻¹ * x * n ∈ S → n⁻¹ * x * n ∈ X)
    (hF8 : ∀ y ∈ S, y * y = 1 → y ∉ X →
      ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ S ⊓ centralizer ({y} : Set G)) :
    ∀ x ∈ X, ∀ h ∈ K, h⁻¹ * x * h ∈ S → h⁻¹ * x * h ∈ X := by
  intro x hx h hh hyS
  by_contra hyX
  set y := h⁻¹ * x * h with hy
  have hSK : S ≤ K := hS.le
  have hSp : IsPGroup 2 S := hS.isPGroup
  obtain ⟨P, hP, hSP⟩ := exists_isSylowOf_two_le (hSp.to_inf_left (K := centralizer ({y} : Set G)))
    (inf_le_inf_right _ hSK)
  obtain ⟨k, hk, hkP⟩ :=
    exists_conj_le_of_isSylowOf hS (hP.le.trans inf_le_left) hP.isPGroup
  have hyP : y ∈ P := hSP ⟨hyS, mem_centralizer_singleton_iff.mpr rfl⟩
  have hy'S : k⁻¹ * y * k ∈ S := hkP y hyP
  by_cases hy'X : k⁻¹ * y * k ∈ X
  ·
    obtain ⟨g, hg⟩ := hF8 y hyS (conj_mul_self_eq_one h x (hX2 x hx)) hyX
    have hgN : g ∈ N := hα g (hg.trans inf_le_left)
    have hkgN : k⁻¹ * g ∈ N := hα (k⁻¹ * g) (by
      rintro _ ⟨a, ha, rfl⟩
      have h1 : g * a * g⁻¹ ∈ P := hSP (hg ⟨a, ha, rfl⟩)
      have h2 := hkP _ h1
      change k⁻¹ * g * a * (k⁻¹ * g)⁻¹ ∈ S
      rwa [show k⁻¹ * g * a * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * a * g⁻¹) * k by group])
    have hkN : k ∈ N := by
      have e : k = g * (k⁻¹ * g)⁻¹ := by group
      rw [e]
      exact N.mul_mem hgN (N.inv_mem hkgN)
    have h3 := hF4 k⁻¹ ⟨N.inv_mem hkN, K.inv_mem hk⟩ _ hy'X (by
      rwa [show k⁻¹⁻¹ * (k⁻¹ * y * k) * k⁻¹ = y by group])
    rw [show k⁻¹⁻¹ * (k⁻¹ * y * k) * k⁻¹ = y by group] at h3
    exact hyX h3
  ·
    have hQ : A.map (MulAut.conj h⁻¹).toMonoidHom ≤ K ⊓ centralizer ({y} : Set G) := by
      rintro _ ⟨a, ha, rfl⟩
      change h⁻¹ * a * h⁻¹⁻¹ ∈ K ⊓ centralizer ({y} : Set G)
      rw [inv_inv]
      refine mem_inf.mpr ⟨K.mul_mem (K.mul_mem (K.inv_mem hh) (hSK (hAS ha))) hh, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have hax : a * x = x * a := (mem_centralizer_iff.mp (hAX ha) x hx).symm
      calc h⁻¹ * a * h * y = h⁻¹ * (a * x) * h := by rw [hy]; group
        _ = h⁻¹ * (x * a) * h := by rw [hax]
        _ = y * (h⁻¹ * a * h) := by rw [hy]; group
    obtain ⟨c, hc, hcQ⟩ :=
      exists_conj_le_of_isSylowOf hP hQ ((hSp.to_le hAS).map (MulAut.conj h⁻¹).toMonoidHom)
    have hcy : c * y = y * c := (mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2)
    have hmN : (h * c * k)⁻¹ ∈ N := hα (h * c * k)⁻¹ (by
      rintro _ ⟨a, ha, rfl⟩
      have h1 := hcQ _ ⟨a, ha, rfl⟩
      change c⁻¹ * (h⁻¹ * a * h⁻¹⁻¹) * c ∈ P at h1
      rw [inv_inv] at h1
      change (h * c * k)⁻¹ * a * (h * c * k)⁻¹⁻¹ ∈ S
      rw [inv_inv]
      have h2 := hkP _ h1
      rwa [show (h * c * k)⁻¹ * a * (h * c * k) = k⁻¹ * (c⁻¹ * (h⁻¹ * a * h) * c) * k by group])
    have hmK : h * c * k ∈ K := K.mul_mem (K.mul_mem hh (mem_inf.mp hc).1) hk
    have hmx : (h * c * k)⁻¹ * x * (h * c * k) = k⁻¹ * y * k := by
      calc (h * c * k)⁻¹ * x * (h * c * k) = k⁻¹ * (c⁻¹ * (y * c)) * k := by rw [hy]; group
        _ = k⁻¹ * y * k := by rw [← hcy]; group
    have h3 := hF4 (h * c * k) ⟨by simpa using N.inv_mem hmN, hmK⟩ x hx (by rwa [hmx])
    rw [hmx] at h3
    exact hy'X h3

theorem forall_conj_mem_of_conj_control_centralizer [Finite G] {L₀ W S R A X : Subgroup G}
    {f : G}
    (hWL : W ≤ centralizer (L₀ : Set G)) (hNW : normalizer (W : Set G) ≤ L₀ ⊔ W)
    (hS : IsSylowOf 2 S ⊤) (hSf : ∀ s ∈ S, s * f = f * s) (hSL : S ≤ L₀) (hfA : f ∈ A)
    (hAX : A ≤ X) (hXS : X ≤ S) (hXab : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hX2 : ∀ x ∈ X, x * x = 1) (hRA : R ≤ centralizer (A : Set G))
    (hα : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ centralizer (W : Set G) →
      g ∈ normalizer (W : Set G))
    (hF4 : ∀ l ∈ L₀ ⊓ centralizer ({f} : Set G), ∀ x ∈ X, l⁻¹ * x * l ∈ X)
    (hF8 : ∀ y ∈ S, y * y = 1 → y ∉ R →
      ∃ l ∈ L₀, A.map (MulAut.conj l).toMonoidHom ≤ S ⊓ centralizer ({y} : Set G)) :
    ∀ x ∈ X, ∀ h ∈ centralizer ({f} : Set G), h⁻¹ * x * h ∈ S → h⁻¹ * x * h ∈ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer ({f} : Set G) with hK
  have hSK : S ≤ K := fun s hs => mem_centralizer_singleton_iff.mpr (hSf s hs)
  have hSyl : IsSylowOf 2 S K := hS.of_le hSK le_top
  have hAS : A ≤ S := hAX.trans hXS
  have hfL : f ∈ L₀ := hSL (hXS (hAX hfA))
  have hLW : L₀ ≤ centralizer (W : Set G) := le_centralizer_iff.mp hWL
  have hAX' : A ≤ centralizer (X : Set G) := fun a ha =>
    mem_centralizer_iff.mpr fun b hb => hXab b hb a (hAX ha)
  have hα' : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ S → g ∈ normalizer (W : Set G) :=
    fun g hg => hα g (hg.trans (hSL.trans hLW))
  have hF4' : ∀ n ∈ normalizer (W : Set G) ⊓ K, ∀ x ∈ X, n⁻¹ * x * n ∈ S →
      n⁻¹ * x * n ∈ X := by
    rintro n ⟨hnN, hnK⟩ x hx -
    have hLN : L₀ ≤ normalizer (W : Set G) :=
      hLW.trans (centralizer_le_normalizer (W : Set G))
    have hn : n ∈ ((L₀ ⊔ W : Subgroup G) : Set G) := hNW hnN
    rw [coe_mul_of_left_le_normalizer_right L₀ W hLN] at hn
    obtain ⟨l, hl, w, hw, rfl⟩ := hn
    have hwf : w * f = f * w := (mem_centralizer_iff.mp (hWL hw) f hfL).symm
    have hlf : l ∈ K := by
      rw [hK, mem_centralizer_singleton_iff]
      have hnf : l * w * f = f * (l * w) := mem_centralizer_singleton_iff.mp hnK
      calc l * f = l * w * f * w⁻¹ := by rw [mul_assoc l w f, hwf]; group
        _ = f * l := by rw [hnf]; group
    have hx' : l⁻¹ * x * l ∈ X := hF4 l ⟨hl, hlf⟩ x hx
    have hcomm : w * (l⁻¹ * x * l) = (l⁻¹ * x * l) * w :=
      (mem_centralizer_iff.mp (hWL hw) _ (hSL (hXS hx'))).symm
    rwa [show (l * w)⁻¹ * x * (l * w) = w⁻¹ * (l⁻¹ * x * l) * w by group, mul_assoc,
      ← hcomm, inv_mul_cancel_left]
  have hF8' : ∀ y ∈ S, y * y = 1 → y ∉ X →
      ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ S ⊓ centralizer ({y} : Set G) := by
    intro y hyS hy2 _
    by_cases hyR : y ∈ R
    · refine ⟨1, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      change 1 * a * 1⁻¹ ∈ S ⊓ centralizer ({y} : Set G)
      rw [one_mul, inv_one, mul_one]
      exact mem_inf.mpr
        ⟨hAS ha, mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hRA hyR) a ha)⟩
    · obtain ⟨l, -, hl⟩ := hF8 y hyS hy2 hyR
      exact ⟨l, hl⟩
  exact stronglyClosed_of_conj_control hSyl hAS hAX' hX2 hα' hF4' hF8'

end CFSG.ComponentClassification.GMS78
