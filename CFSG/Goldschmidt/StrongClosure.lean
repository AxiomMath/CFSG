module

public import CFSG.Open.FusionDefs

public section

namespace CFSG.Goldschmidt

open Subgroup

variable {X : Type*} [Group X]

@[expose] def conjSub (g : X) (A : Subgroup X) : Subgroup X :=
  A.map (MulAut.conj g⁻¹).toMonoidHom

theorem mem_conjSub {g : X} {A : Subgroup X} {x : X} :
    x ∈ conjSub g A ↔ g * x * g⁻¹ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [mul_assoc] using ha
  · intro h
    refine ⟨g * x * g⁻¹, h, ?_⟩
    simp [mul_assoc]

theorem conj_mem_conjSub {g : X} {A : Subgroup X} {a : X} (ha : a ∈ A) :
    g⁻¹ * a * g ∈ conjSub g A :=
  mem_conjSub.2 (by simpa [mul_assoc] using ha)

theorem card_conjSub (g : X) (A : Subgroup X) : Nat.card (conjSub g A) = Nat.card A :=
  Nat.card_congr (A.equivMapOfInjective _ (MulAut.conj g⁻¹).injective).symm.toEquiv

section Closure

variable {S A : Subgroup X}

theorem conj_mem_of_stronglyClosed (hAS : A ≤ S)
    (hcl : CFSG.Open.fusionStronglyClosed (A : Set X) S) {s : X} (hs : s ∈ S) {a : X}
    (ha : a ∈ A) : s⁻¹ * a * s ∈ A :=
  hcl a ha s (S.mul_mem (S.mul_mem (S.inv_mem hs) (hAS ha)) hs)

theorem normal_subgroupOf_of_stronglyClosed (hAS : A ≤ S)
    (hcl : CFSG.Open.fusionStronglyClosed (A : Set X) S) : (A.subgroupOf S).Normal where
  conj_mem n hn s := by
    have := conj_mem_of_stronglyClosed hAS hcl (S.inv_mem s.2) hn
    simpa [Subgroup.mem_subgroupOf] using this

theorem conj_eq_of_conj_le [Finite X] (hcl : CFSG.Open.fusionStronglyClosed (A : Set X) S)
    {g : X} (hg : conjSub g A ≤ S) : conjSub g A = A := by
  have hle : conjSub g A ≤ A := by
    intro x hx
    have hxa : g * x * g⁻¹ ∈ A := mem_conjSub.1 hx
    have hx' : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    have := hcl _ hxa g (by rw [hx']; exact hg hx)
    rwa [hx'] at this
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])

theorem stronglyClosed_conj [Finite X] (hcl : CFSG.Open.fusionStronglyClosed (A : Set X) S)
    {g : X} (hgA : conjSub g A = A) :
    CFSG.Open.fusionStronglyClosed (A : Set X) (S.map (MulAut.conj g).toMonoidHom) := by
  intro a ha h hh
  obtain ⟨y, hy, hyeq⟩ := hh
  have hy' : y = (h * g)⁻¹ * a * (h * g) := by
    have : g * y * g⁻¹ = h⁻¹ * a * h := by simpa [MulAut.conj_apply] using hyeq
    calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
      _ = (h * g)⁻¹ * a * (h * g) := by rw [this]; group
  have hyA : y ∈ A := by
    have := hcl a ha (h * g) (by rw [← hy']; exact hy)
    rwa [← hy'] at this
  have : h⁻¹ * a * h = g * y * g⁻¹ := by rw [hy']; group
  rw [this]
  have hy2 : y ∈ conjSub g A := by rw [hgA]; exact hyA
  exact mem_conjSub.1 hy2

theorem stronglyClosed_of_le_sylow {p : ℕ} [Fact p.Prime] [Finite X] (P Q : Sylow p X)
    (hcl : CFSG.Open.fusionStronglyClosed (A : Set X) (P : Subgroup X)) (hAQ : A ≤ Q) :
    CFSG.Open.fusionStronglyClosed (A : Set X) (Q : Subgroup X) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P Q
  have hQ : (Q : Subgroup X) = (P : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]; rfl
  have hgA : conjSub g A = A := by
    refine conj_eq_of_conj_le hcl fun x hx => ?_
    have hxa : g * x * g⁻¹ ∈ (Q : Subgroup X) := hAQ (mem_conjSub.1 hx)
    rw [hQ] at hxa
    obtain ⟨y, hy, hyeq⟩ := hxa
    have : y = x := by
      have h1 : g * y * g⁻¹ = g * x * g⁻¹ := by simpa [MulAut.conj_apply] using hyeq
      simpa using h1
    rwa [← this]
  rw [hQ]
  exact stronglyClosed_conj hcl hgA

theorem stronglyClosed_of_le_pGroup {p : ℕ} [Fact p.Prime] [Finite X] (P : Sylow p X)
    (hcl : CFSG.Open.fusionStronglyClosed (A : Set X) (P : Subgroup X)) {R : Subgroup X}
    (hR : IsPGroup p R) (hAR : A ≤ R) :
    ∃ Q : Sylow p X, R ≤ Q ∧ CFSG.Open.fusionStronglyClosed (A : Set X) (Q : Subgroup X) := by
  obtain ⟨Q, hRQ⟩ := hR.exists_le_sylow
  exact ⟨Q, hRQ, stronglyClosed_of_le_sylow P Q hcl (hAR.trans hRQ)⟩

theorem stronglyClosed_subgroupOf {p : ℕ} [Fact p.Prime] [Finite X] (P : Sylow p X)
    (hcl : CFSG.Open.fusionStronglyClosed (A : Set X) (P : Subgroup X)) {H : Subgroup X}
    (hAH : A ≤ H) (T : Sylow p H) (hAT : A.subgroupOf H ≤ T) :
    CFSG.Open.fusionStronglyClosed ((A.subgroupOf H : Subgroup H) : Set H)
      (T : Subgroup H) := by
  have hTp : IsPGroup p ((T : Subgroup H).map H.subtype) := T.2.map _
  have hAT' : A ≤ (T : Subgroup H).map H.subtype := by
    intro a ha
    exact ⟨⟨a, hAH ha⟩, hAT (by simpa [Subgroup.mem_subgroupOf] using ha), rfl⟩
  obtain ⟨Q, hTQ, hQ⟩ := stronglyClosed_of_le_pGroup P hcl hTp hAT'
  intro a ha h hh
  have hmem : ((h⁻¹ * a * h : H) : X) ∈ (T : Subgroup H).map H.subtype := ⟨_, hh, rfl⟩
  have := hQ (a : X) ha (h : X) (hTQ (by simpa using hmem))
  simpa [Subgroup.mem_subgroupOf] using this

theorem conjSub_mul (x y : X) (A : Subgroup X) : conjSub (x * y) A = conjSub y (conjSub x A) := by
  ext z
  simp only [mem_conjSub]
  constructor <;> intro h <;> simpa [mul_assoc] using h

theorem conjSub_one (A : Subgroup X) : conjSub 1 A = A := by
  ext z
  simp [mem_conjSub]

theorem exists_conj_normalClosure {p : ℕ} [Fact p.Prime] [Finite X] (P : Sylow p X)
    (hAP : A ≤ P) (hcl : CFSG.Open.fusionStronglyClosed (A : Set X) (P : Subgroup X)) (x : X) :
    ∃ m ∈ Subgroup.normalClosure (A : Set X), conjSub x A = conjSub m A := by
  set M := Subgroup.normalClosure (A : Set X) with hMdef
  have hAM : A ≤ M := Subgroup.le_normalClosure
  have hxAM : conjSub x A ≤ M := by
    intro z hz
    have hz' : x * z * x⁻¹ ∈ M := hAM (mem_conjSub.1 hz)
    have := (Subgroup.normalClosure_normal (s := (A : Set X))).conj_mem _ hz' x⁻¹
    simpa [mul_assoc] using this
  have hpA : IsPGroup p A := P.2.to_le hAP
  have hpB : IsPGroup p (conjSub x A) := hpA.map _
  obtain ⟨R', hR'⟩ := (hpA.comap_subtype (K := M)).exists_le_sylow
  obtain ⟨R, hR⟩ := (hpB.comap_subtype (K := M)).exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M R' R
  have hR'X : IsPGroup p ((R' : Subgroup M).map M.subtype) := R'.2.map _
  have hAR' : A ≤ (R' : Subgroup M).map M.subtype := fun a ha =>
    ⟨⟨a, hAM ha⟩, hR' (Subgroup.mem_subgroupOf.2 ha), rfl⟩
  obtain ⟨Q, hRQ, hQ⟩ := stronglyClosed_of_le_pGroup P hcl hR'X hAR'
  have hle : conjSub (x * (m : X)) A ≤ Q := by
    intro z hz
    rw [conjSub_mul, mem_conjSub] at hz
    have hzM : (m : X) * z * (m : X)⁻¹ ∈ M := hxAM hz
    have hzR : (⟨_, hzM⟩ : M) ∈ (R : Subgroup M) := hR (Subgroup.mem_subgroupOf.2 hz)
    rw [← hm] at hzR
    obtain ⟨w, hw, hweq⟩ := hzR
    have hwz : (w : X) = z := by
      have := congrArg Subtype.val hweq
      have h2 : (m : X) * w * (m : X)⁻¹ = (m : X) * z * (m : X)⁻¹ := this
      simpa using h2
    exact hRQ ⟨w, hw, hwz⟩
  have heq := conj_eq_of_conj_le hQ hle
  refine ⟨(m : X)⁻¹, M.inv_mem m.2, ?_⟩
  rw [conjSub_mul] at heq
  calc conjSub x A = conjSub ((m : X) * (m : X)⁻¹) (conjSub x A) := by
        rw [mul_inv_cancel, conjSub_one]
    _ = conjSub (m : X)⁻¹ A := by rw [conjSub_mul, heq]

theorem stronglyClosed_inf_normal (hcl : CFSG.Open.fusionStronglyClosed (A : Set X) S)
    (N : Subgroup X) [N.Normal] : CFSG.Open.fusionStronglyClosed ((A ⊓ N : Subgroup X) : Set X) S :=
  fun a ha g hg => ⟨hcl a ha.1 g hg, by
    have := (inferInstance : N.Normal).conj_mem a ha.2 g⁻¹
    simpa using this⟩

theorem stronglyClosed_sq_eq_one (hcl : CFSG.Open.fusionStronglyClosed (A : Set X) S) :
    CFSG.Open.fusionStronglyClosed {a | a ∈ A ∧ a ^ 2 = 1} S := by
  rintro a ⟨ha, ha2⟩ g hg
  refine ⟨hcl a ha g hg, ?_⟩
  rw [sq] at ha2 ⊢
  calc g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
    _ = 1 := by rw [ha2]; group

theorem isTI_iff_centralizer_le_normalizer {p : ℕ} [Fact p.Prime] [Finite X] (P : Sylow p X)
    {V : Subgroup X} (hVP : V ≤ P) (hcl : CFSG.Open.fusionStronglyClosed (V : Set X) P)
    (hab : IsMulCommutative V) :
    CFSG.Open.fusionIsTI V ↔ ∀ v ∈ V, v ≠ 1 →
      Subgroup.centralizer ({v} : Set X) ≤ Subgroup.normalizer (V : Set X) := by
  constructor
  · intro hTI v hv hv1 g hg
    rw [Subgroup.mem_normalizer_iff]
    by_contra hne
    have hmap : V.map (MulAut.conj g).toMonoidHom ≠ V := by
      intro heq
      apply hne
      intro h
      constructor
      · intro hh
        have : g * h * g⁻¹ ∈ V.map (MulAut.conj g).toMonoidHom := ⟨h, hh, rfl⟩
        rwa [heq] at this
      · intro hh
        have hh' : g * h * g⁻¹ ∈ V.map (MulAut.conj g).toMonoidHom := by rw [heq]; exact hh
        obtain ⟨y, hy, hyeq⟩ := hh'
        have : y = h := by
          have h1 : g * y * g⁻¹ = g * h * g⁻¹ := by simpa [MulAut.conj_apply] using hyeq
          simpa using h1
        rwa [← this]
    have hvmem : v ∈ V ⊓ V.map (MulAut.conj g).toMonoidHom := by
      refine ⟨hv, v, hv, ?_⟩
      have := Subgroup.mem_centralizer_iff.1 hg v (Set.mem_singleton v)
      show g * v * g⁻¹ = v
      rw [← this, mul_inv_cancel_right]
    rw [hTI g hmap] at hvmem
    exact hv1 ((Subgroup.mem_bot).1 hvmem)
  · intro hC g hg
    rw [eq_bot_iff]
    intro v hv
    rw [Subgroup.mem_bot]
    by_contra hv1
    obtain ⟨hvV, w, hwV, hwv⟩ := hv
    have hWle : V.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (V : Set X) := by
      intro y hy
      apply hC v hvV hv1
      rw [Subgroup.mem_centralizer_iff]
      rintro z rfl
      obtain ⟨u, hu, rfl⟩ := hy
      have hcomm := hab.is_comm.comm ⟨u, hu⟩ ⟨w, hwV⟩
      have hcomm' : u * w = w * u := congrArg Subtype.val hcomm
      rw [← hwv]
      show g * w * g⁻¹ * (g * u * g⁻¹) = g * u * g⁻¹ * (g * w * g⁻¹)
      calc g * w * g⁻¹ * (g * u * g⁻¹) = g * (w * u) * g⁻¹ := by group
        _ = g * (u * w) * g⁻¹ := by rw [hcomm']
        _ = g * u * g⁻¹ * (g * w * g⁻¹) := by group
    have hp : IsPGroup p ↥(V ⊔ V.map (MulAut.conj g).toMonoidHom) :=
      (P.2.to_le hVP).to_sup_of_normal_left' ((P.2.to_le hVP).map _) hWle
    obtain ⟨Q, hQle, hQ⟩ := stronglyClosed_of_le_pGroup P hcl hp le_sup_left
    have hle : conjSub g⁻¹ V ≤ Q := by
      intro z hz
      apply hQle
      have hzV : g⁻¹ * z * g ∈ V := by simpa using (mem_conjSub.1 hz)
      have hz' : z ∈ V.map (MulAut.conj g).toMonoidHom :=
        ⟨g⁻¹ * z * g, hzV, by simp [MulAut.conj_apply, mul_assoc]⟩
      exact Subgroup.mem_sup_right hz'
    have heq := conj_eq_of_conj_le hQ hle
    apply hg
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : (MulAut.conj g).toMonoidHom y ∈ conjSub g⁻¹ V := by
        rw [mem_conjSub]; simpa [MulAut.conj_apply, mul_assoc] using hy
      rwa [heq] at this
    · intro hz
      have hz' : z ∈ conjSub g⁻¹ V := by rw [heq]; exact hz
      refine ⟨g⁻¹ * z * g, by simpa [mem_conjSub, mul_assoc] using hz', ?_⟩
      simp [MulAut.conj_apply, mul_assoc]

end Closure

end CFSG.Goldschmidt
