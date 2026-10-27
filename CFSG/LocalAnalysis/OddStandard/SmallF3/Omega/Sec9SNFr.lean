module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec9n_frattini [Finite G] {K A : Subgroup G} (hA : IsSylow2Of A K) {m : G}
    (hm : ∀ x : G, x ∈ K ↔ m * x * m⁻¹ ∈ K) :
    ∃ c ∈ K, ∀ h : G, h ∈ A ↔ (c * m) * h * (c * m)⁻¹ ∈ A := by
  let A' : Subgroup G := A.map (MulAut.conj m).toMonoidHom
  have hmA' : ∀ x : G, x ∈ A' ↔ m⁻¹ * x * m ∈ A := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
      simpa [MulAut.conj_apply, mul_assoc] using ha
    · intro hx
      exact Subgroup.mem_map.2 ⟨m⁻¹ * x * m, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hAci : CFSG.ClassicalInvolution.IsSylow2Of A K := isSylow2Of_iff_ci.1 hA
  have hA'ci : CFSG.ClassicalInvolution.IsSylow2Of A' K := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      have hx' : m⁻¹ * x * m ∈ A := (hmA' x).1 hx
      have hK : m * (m⁻¹ * x * m) * m⁻¹ ∈ K := (hm (m⁻¹ * x * m)).1 (hA.1 hx')
      have hx : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
      simpa [hx] using hK
    · exact hA.2.1.map (MulAut.conj m).toMonoidHom
    · intro P' hP'K hP'2 hle
      have hAQ : A ≤ P'.map (MulAut.conj m⁻¹).toMonoidHom := by
        intro a ha
        refine Subgroup.mem_map.2 ⟨m * a * m⁻¹,
          hle (Subgroup.mem_map.2 ⟨a, ha, rfl⟩), ?_⟩
        simp [MulAut.conj_apply, mul_assoc]
      have hQK : P'.map (MulAut.conj m⁻¹).toMonoidHom ≤ K := by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hx
        have hp' : m * (m⁻¹ * p * m) * m⁻¹ ∈ K := by
          have hpeq : m * (m⁻¹ * p * m) * m⁻¹ = p := by group
          rw [hpeq]
          exact hP'K hp
        simpa [MulAut.conj_apply] using (hm (m⁻¹ * p * m)).2 hp'
      have hQ2 : IsPGroup 2 (P'.map (MulAut.conj m⁻¹).toMonoidHom) :=
        hP'2.map (MulAut.conj m⁻¹).toMonoidHom
      have hQeq : P'.map (MulAut.conj m⁻¹).toMonoidHom = A :=
        hAci.2.2 _ hQK hQ2 hAQ
      have hcomp : (MulAut.conj m).toMonoidHom.comp (MulAut.conj m⁻¹).toMonoidHom =
          MonoidHom.id G := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      calc P' = (P'.map (MulAut.conj m⁻¹).toMonoidHom).map (MulAut.conj m).toMonoidHom := by
            rw [Subgroup.map_map, hcomp, Subgroup.map_id]
        _ = A.map (MulAut.conj m).toMonoidHom := by rw [hQeq]
        _ = A' := rfl
  have hA' : IsSylow2Of A' K := isSylow2Of_iff_ci.2 hA'ci
  obtain ⟨a, haK, ha⟩ := hA'.exists_conj_mem hA
  refine ⟨a, haK, fun h => ?_⟩
  have h1 : a⁻¹ * ((a * m) * h * (a * m)⁻¹) * a = m * h * m⁻¹ := by group
  have h2 : m⁻¹ * (m * h * m⁻¹) * m = h := by group
  have hkey : m * h * m⁻¹ ∈ A' ↔ (a * m) * h * (a * m)⁻¹ ∈ A := by
    have h := ha ((a * m) * h * (a * m)⁻¹)
    rw [h1] at h
    exact h.symm
  have hmid : h ∈ A ↔ m * h * m⁻¹ ∈ A' := by
    have h := hmA' (m * h * m⁻¹)
    rw [h2] at h
    exact h.symm
  exact hmid.trans hkey

private theorem sec9n_centralizer_conj_normalizer {A8 : Subgroup G} {n x : G}
    (hn : n ∈ normalizer (A8 : Set G)) :
    x ∈ centralizer (A8 : Set G) ↔ n * x * n⁻¹ ∈ centralizer (A8 : Set G) := by
  have hn' : n⁻¹ ∈ normalizer (A8 : Set G) := (normalizer (A8 : Set G)).inv_mem hn
  have key : ∀ h : G, h ∈ A8 ↔ n * h * n⁻¹ ∈ A8 := Subgroup.mem_normalizer_iff.mp hn
  have key' : ∀ h : G, h ∈ A8 ↔ n⁻¹ * h * n ∈ A8 := by
    intro h
    simpa using Subgroup.mem_normalizer_iff.mp hn' h
  constructor
  · intro hx h hh
    have hx' := (Subgroup.mem_centralizer_iff.mp hx) (n⁻¹ * h * n) ((key' h).mp hh)
    calc h * (n * x * n⁻¹) = n * ((n⁻¹ * h * n) * x) * n⁻¹ := by group
      _ = n * (x * (n⁻¹ * h * n)) * n⁻¹ := by rw [hx']
      _ = (n * x * n⁻¹) * h := by group
  · intro hx h hh
    have hx' := (Subgroup.mem_centralizer_iff.mp hx) (n * h * n⁻¹) ((key h).mp hh)
    have hxh : h * x = x * h := by
      have := congrArg (fun z => n⁻¹ * z * n) hx'
      simpa [mul_assoc] using this
    exact hxh

theorem sec9n_P_twoTrans [Finite G] {A8 A : Subgroup G} {T : Set G} (hTA8 : T ⊆ A8)
    (hsyl : IsSylow2Of A (centralizer (A8 : Set G)))
    (hM : ConjTwoTransOn (normalizer (A8 : Set G)) T) :
    ConjTwoTransOn (normalizer (A8 : Set G) ⊓ normalizer (A : Set G)) T := by
  refine ⟨?_, ?_⟩
  · intro n hn a ha
    exact hM.1 n hn.1 a ha
  · intro a ha b hb c hc d hd hab hcd
    obtain ⟨n, hnN, hna, hnb⟩ := hM.2 a ha b hb c hc d hd hab hcd
    have hK : ∀ x : G, x ∈ centralizer (A8 : Set G) ↔
        n * x * n⁻¹ ∈ centralizer (A8 : Set G) :=
      fun x => sec9n_centralizer_conj_normalizer (x := x) hnN
    obtain ⟨c₀, hc₀K, hc₀A⟩ := sec9n_frattini hsyl hK
    refine ⟨c₀ * n, ⟨?_, ?_⟩, ?_, ?_⟩
    · exact (normalizer (A8 : Set G)).mul_mem
        (Subgroup.centralizer_le_normalizer (A8 : Set G) hc₀K) hnN
    · exact Subgroup.mem_normalizer_iff.mpr hc₀A
    · have hcc₀ : c * c₀ = c₀ * c :=
        Subgroup.mem_centralizer_iff.mp hc₀K c (hTA8 hc)
      calc (c₀ * n) * a * (c₀ * n)⁻¹ = c₀ * (n * a * n⁻¹) * c₀⁻¹ := by group
        _ = c₀ * c * c₀⁻¹ := by rw [hna]
        _ = c := by rw [← hcc₀]; group
    · have hdd₀ : d * c₀ = c₀ * d :=
        Subgroup.mem_centralizer_iff.mp hc₀K d (hTA8 hd)
      calc (c₀ * n) * b * (c₀ * n)⁻¹ = c₀ * (n * b * n⁻¹) * c₀⁻¹ := by group
        _ = c₀ * d * c₀⁻¹ := by rw [hnb]
        _ = d := by rw [← hdd₀]; group

theorem sec9n_M_le_normalizer_B {t : G} {B : Subgroup G} (ht2 : t * t = 1)
    (htB : ∀ b ∈ B, t * b = b * t)
    (hM : ConjTwoTransOn (normalizer ((zpowers t ⊔ B : Subgroup G) : Set G)) (cosetSet t B)) :
    normalizer ((zpowers t ⊔ B : Subgroup G) : Set G) ≤ normalizer (B : Set G) := by
  have hconj : ∀ m ∈ normalizer ((zpowers t ⊔ B : Subgroup G) : Set G),
      ∀ b ∈ B, m * b * m⁻¹ ∈ B := by
    intro m hm b hb
    have ht : t ∈ cosetSet t B := ⟨1, B.one_mem, by simp⟩
    have htb : t * b ∈ cosetSet t B := ⟨b, hb, rfl⟩
    obtain ⟨b₁, hb₁, hb₁eq⟩ := hM.1 m hm t ht
    obtain ⟨b₂, hb₂, hb₂eq⟩ := hM.1 m hm (t * b) htb
    have heq : m * b * m⁻¹ = b₁⁻¹ * b₂ := by
      calc m * b * m⁻¹ = (m * t * m⁻¹)⁻¹ * (m * (t * b) * m⁻¹) := by group
        _ = (t * b₁)⁻¹ * (t * b₂) := by rw [hb₁eq, hb₂eq]
        _ = b₁⁻¹ * b₂ := by group
    rw [heq]
    exact B.mul_mem (B.inv_mem hb₁) hb₂
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · exact hconj m hm b
  · intro hb
    have := hconj m⁻¹ ((normalizer ((zpowers t ⊔ B : Subgroup G) : Set G)).inv_mem hm)
      (m * b * m⁻¹) hb
    simpa [mul_assoc] using this

theorem sec9n_ncard_coset {t : G} {B : Subgroup G} (hB : Nat.card B = 16) :
    (cosetSet t B).ncard = 16 := by
  have hset : cosetSet t B = (fun b : G => t * b) '' (B : Set G) := by
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, rfl⟩
  rw [hset, Set.ncard_image_of_injective (B : Set G) (mul_right_injective t)]
  rw [← Nat.card_coe_set_eq]
  exact hB

end CFSG.OddStandard.SmallF3.Omega
