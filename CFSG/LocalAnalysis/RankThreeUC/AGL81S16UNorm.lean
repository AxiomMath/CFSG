module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16NormIdx
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16QModel
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Data

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup Matrix

variable {G : Type} [Group G]

@[expose] def conjOn (V : Subgroup G) (m : G) (hm : m ∈ normalizer (V : Set G)) : ↥V ≃* ↥V where
  toFun v := ⟨m * (v : G) * m⁻¹, (mem_normalizer_iff.mp hm v).mp v.2⟩
  invFun v := ⟨m⁻¹ * (v : G) * m, by
    have := (mem_normalizer_iff.mp ((normalizer (V : Set G)).inv_mem hm) v).mp v.2
    simpa using this⟩
  left_inv v := Subtype.ext (by simp [mul_assoc])
  right_inv v := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

@[simp] theorem coe_conjOn (V : Subgroup G) (m : G) (hm : m ∈ normalizer (V : Set G)) (v : ↥V) :
    ((conjOn V m hm v : ↥V) : G) = m * (v : G) * m⁻¹ := rfl

section Act

variable {n : ℕ} {L V : Subgroup G} (d : U4NatData G n L V)

@[expose] noncomputable def U4NatData.eqv : ↥V ≃ (Fin 4 → d.F) :=
  (MulEquiv.ofBijective d.φ d.φ_bij).toEquiv.trans Multiplicative.toAdd

theorem U4NatData.eqv_apply (v : ↥V) : d.eqv v = Multiplicative.toAdd (d.φ v) := rfl

theorem U4NatData.eqv_mul (v w : ↥V) : d.eqv (v * w) = d.eqv v + d.eqv w := by
  simp [U4NatData.eqv_apply, map_mul, toAdd_mul]

@[expose] noncomputable def U4NatData.act (m : G) (hm : m ∈ normalizer (V : Set G)) :
    Equiv.Perm (Fin 4 → d.F) :=
  d.eqv.permCongr (conjOn V m hm).toEquiv

theorem U4NatData.act_eqv (m : G) (hm : m ∈ normalizer (V : Set G)) (v : ↥V) :
    d.act m hm (d.eqv v) = d.eqv (conjOn V m hm v) := by
  simp [U4NatData.act, Equiv.permCongr_apply]

theorem U4NatData.act_add (m : G) (hm : m ∈ normalizer (V : Set G)) (x y : Fin 4 → d.F) :
    d.act m hm (x + y) = d.act m hm x + d.act m hm y := by
  obtain ⟨v, rfl⟩ := d.eqv.surjective x
  obtain ⟨w, rfl⟩ := d.eqv.surjective y
  rw [← d.eqv_mul, d.act_eqv, d.act_eqv, d.act_eqv, ← d.eqv_mul, map_mul]

noncomputable def U4NatData.rho (A : Subgroup G) (hA : A ≤ normalizer (V : Set G)) :
    ↥A →* Equiv.Perm (Fin 4 → d.F) where
  toFun a := d.act a.1 (hA a.2)
  map_one' := Equiv.ext fun x => by
    obtain ⟨v, rfl⟩ := d.eqv.surjective x
    show d.act _ _ (d.eqv v) = d.eqv v
    rw [d.act_eqv]
    exact congrArg d.eqv (Subtype.ext (by simp))
  map_mul' a b := Equiv.ext fun x => by
    obtain ⟨v, rfl⟩ := d.eqv.surjective x
    show d.act _ _ (d.eqv v) = d.act _ _ (d.act _ _ (d.eqv v))
    rw [d.act_eqv, d.act_eqv, d.act_eqv]
    exact congrArg d.eqv (Subtype.ext (by simp [mul_assoc]))

theorem U4NatData.rho_eqv (A : Subgroup G) (hA : A ≤ normalizer (V : Set G)) (a : ↥A)
    (v : ↥V) : d.rho A hA a (d.eqv v) = d.eqv (conjOn V a.1 (hA a.2) v) :=
  d.act_eqv a.1 (hA a.2) v

theorem U4NatData.eps_eqv {l : G} (hl : l ∈ L) (hlV : l ∈ normalizer (V : Set G)) (v : ↥V) :
    ((d.ε ⟨l, hl⟩ : GL (Fin 4) d.F) : Matrix (Fin 4) (Fin 4) d.F) *ᵥ d.eqv v =
      d.eqv (conjOn V l hlV v) := by
  have h := d.equiv ⟨l, hl⟩ v (conjOn V l hlV v) rfl
  have := congrArg Multiplicative.toAdd h
  rw [toAdd_ofAdd] at this
  exact this.symm

theorem U4NatData.act_eps {l m : G} (hl : l ∈ L) (hlV : l ∈ normalizer (V : Set G))
    (hml : m * l * m⁻¹ ∈ L) (hmlV : m * l * m⁻¹ ∈ normalizer (V : Set G))
    (hm : m ∈ normalizer (V : Set G)) (x : Fin 4 → d.F) :
    d.act m hm (((d.ε ⟨l, hl⟩ : GL (Fin 4) d.F) : Matrix (Fin 4) (Fin 4) d.F) *ᵥ x) =
      ((d.ε ⟨m * l * m⁻¹, hml⟩ : GL (Fin 4) d.F) : Matrix (Fin 4) (Fin 4) d.F) *ᵥ
        d.act m hm x := by
  obtain ⟨v, rfl⟩ := d.eqv.surjective x
  rw [d.eps_eqv hl hlV, d.act_eqv, d.act_eqv, d.eps_eqv hml hmlV]
  exact congrArg d.eqv (Subtype.ext (by simp [mul_assoc]))

end Act

section Facts

variable {n : ℕ} {M L V : Subgroup G} (d : U4NatData G n L V)

theorem U4NatData.act_normalizes (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hMV : M ≤ normalizer (V : Set G)) {m : G} (hm : m ∈ M) :
    ∀ g ∈ StatedSU 4 (2 ^ n) d.F, ∃ g' ∈ StatedSU 4 (2 ^ n) d.F, ∀ x : Fin 4 → d.F,
      d.act m (hMV hm) (((g : GL (Fin 4) d.F) : Matrix (Fin 4) (Fin 4) d.F) *ᵥ x) =
        ((g' : GL (Fin 4) d.F) : Matrix (Fin 4) (Fin 4) d.F) *ᵥ d.act m (hMV hm) x := by
  intro g hg
  obtain ⟨l, hl⟩ := d.ε_surj ⟨g, hg⟩
  have hlL : (l : G) ∈ L := l.2
  have hmlL : m * (l : G) * m⁻¹ ∈ L := (mem_normalizer_iff.mp (hML hm) l).mp hlL
  refine ⟨(d.ε ⟨m * l * m⁻¹, hmlL⟩ : GL (Fin 4) d.F), (d.ε ⟨m * l * m⁻¹, hmlL⟩).2, fun x => ?_⟩
  have h := d.act_eps (l := l) (m := m) hlL (hMV (hLM hlL)) hmlL (hMV (hLM hmlL)) (hMV hm) x
  have hg' : ((d.ε l : ↥(StatedSU 4 (2 ^ n) d.F)) : GL (Fin 4) d.F) = g := congrArg Subtype.val hl
  rw [← hg']
  exact h

@[expose] noncomputable def U4NatData.actAdd (m : G) (hm : m ∈ normalizer (V : Set G)) :
    (Fin 4 → d.F) ≃+ (Fin 4 → d.F) :=
  { toEquiv := d.act m hm, map_add' := d.act_add m hm }

theorem U4NatData.actAdd_apply (m : G) (hm : m ∈ normalizer (V : Set G)) (x : Fin 4 → d.F) :
    d.actAdd m hm x = d.act m hm x := rfl

theorem U4NatData.act_inv_act (m : G) (hm : m ∈ normalizer (V : Set G)) (x : Fin 4 → d.F) :
    d.act m hm (d.act m⁻¹ ((normalizer (V : Set G)).inv_mem hm) x) = x := by
  obtain ⟨v, rfl⟩ := d.eqv.surjective x
  rw [d.act_eqv, d.act_eqv]
  exact congrArg d.eqv (Subtype.ext (by simp [mul_assoc]))

theorem U4NatData.actAdd_symm (m : G) (hm : m ∈ normalizer (V : Set G)) (y : Fin 4 → d.F) :
    (d.actAdd m hm).symm y = d.act m⁻¹ ((normalizer (V : Set G)).inv_mem hm) y := by
  rw [AddEquiv.symm_apply_eq, d.actAdd_apply, d.act_inv_act]

include d in
theorem U4NatData.inv_index [Finite G] (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hMV : M ≤ normalizer (V : Set G)) :
    ∀ t ∈ M, t ∉ centralizer (V : Set G) →
      2 ^ (2 * n) ≤ (V ⊓ centralizer ({t} : Set G)).relIndex V := by
  intro t ht htc
  haveI : Finite d.F := inferInstance
  obtain ⟨θ, hθ⟩ := exists_semilinear_statedSU d.card_F (d.actAdd t (hMV ht))
    (fun g hg => by
      obtain ⟨g', hg', hg'x⟩ := d.act_normalizes hLM hML hMV (inv_mem ht) g hg
      exact ⟨g', hg', fun x => by rw [d.actAdd_symm, d.actAdd_symm]; exact hg'x x⟩)
  have hne : ∃ x, d.actAdd t (hMV ht) x ≠ x := by
    obtain ⟨v, hv, hvt⟩ : ∃ v ∈ V, ¬ v * t = t * v := by
      by_contra hcon
      push Not at hcon
      exact htc (Subgroup.mem_centralizer_iff.mpr fun v hv => hcon v hv)
    refine ⟨d.eqv ⟨v, hv⟩, fun h => hvt ?_⟩
    rw [d.actAdd_apply, d.act_eqv] at h
    have h2 : (conjOn V t (hMV ht) ⟨v, hv⟩ : ↥V) = ⟨v, hv⟩ := d.eqv.injective h
    have h3 : t * v * t⁻¹ = v := congrArg Subtype.val h2
    calc v * t = (t * v * t⁻¹) * t := by rw [h3]
      _ = t * v := by group
  have hfix := card_fix_mul_le (d.actAdd t (hMV ht)) hθ hne
  have hcard : Nat.card ↥(V ⊓ centralizer ({t} : Set G)) =
      Nat.card {x : Fin 4 → d.F // d.actAdd t (hMV ht) x = x} := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun c => ⟨d.eqv ⟨(c : G), c.2.1⟩, ?_⟩) ⟨?_, ?_⟩)
    · have hc : t * (c : G) = (c : G) * t := Subgroup.mem_centralizer_iff.mp c.2.2 t rfl
      show d.act t (hMV ht) (d.eqv ⟨(c : G), c.2.1⟩) = d.eqv ⟨(c : G), c.2.1⟩
      rw [d.act_eqv]
      exact congrArg d.eqv (Subtype.ext (by
        show t * (c : G) * t⁻¹ = (c : G)
        rw [hc]; group))
    · intro c c' h
      have h1 : d.eqv ⟨(c : G), c.2.1⟩ = d.eqv ⟨(c' : G), c'.2.1⟩ := congrArg Subtype.val h
      exact Subtype.ext (congrArg (fun z : ↥V => (z : G)) (d.eqv.injective h1))
    · rintro ⟨x, hx⟩
      obtain ⟨v, rfl⟩ := d.eqv.surjective x
      rw [d.actAdd_apply, d.act_eqv] at hx
      have h2 : (conjOn V t (hMV ht) v : ↥V) = v := d.eqv.injective hx
      have h3 : t * (v : G) * t⁻¹ = v := congrArg Subtype.val h2
      refine ⟨⟨(v : G), v.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩, rfl⟩
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      calc t * (v : G) = (t * (v : G) * t⁻¹) * t := by group
        _ = (v : G) * t := by rw [h3]
  have hV : Nat.card ↥V = Nat.card (Fin 4 → d.F) := Nat.card_congr d.eqv
  have hmul := Subgroup.relIndex_mul_card (H := V ⊓ centralizer ({t} : Set G)) (K := V)
  rw [inf_eq_left.mpr (inf_le_left : V ⊓ centralizer ({t} : Set G) ≤ V)] at hmul
  have hpos : 0 < Nat.card ↥(V ⊓ centralizer ({t} : Set G)) := Nat.card_pos
  have h2n : Nat.card d.F = 2 ^ (2 * n) := by rw [d.card_F, ← pow_mul, mul_comm]
  rw [← hcard] at hfix
  have h3 : Nat.card d.F * Nat.card ↥(V ⊓ centralizer ({t} : Set G)) ≤
      (V ⊓ centralizer ({t} : Set G)).relIndex V *
        Nat.card ↥(V ⊓ centralizer ({t} : Set G)) :=
    calc Nat.card d.F * Nat.card ↥(V ⊓ centralizer ({t} : Set G))
        = Nat.card ↥(V ⊓ centralizer ({t} : Set G)) * Nat.card d.F := mul_comm _ _
      _ ≤ Nat.card (Fin 4 → d.F) := hfix
      _ = Nat.card ↥V := hV.symm
      _ = (V ⊓ centralizer ({t} : Set G)).relIndex V *
          Nat.card ↥(V ⊓ centralizer ({t} : Set G)) := hmul.symm
  rw [← h2n]
  exact Nat.le_of_mul_le_mul_right h3 hpos

include d in
theorem U4NatData.Q_le [Finite G] (hn : 1 ≤ n) (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hMV : M ≤ normalizer (V : Set G)) :
    ∀ A : Subgroup G, A ≤ M → IsElemAbelian 2 A →
      (∀ B : Subgroup G, B ≤ A → B.relIndex A < 2 ^ (2 * n) →
        V ⊓ centralizer (B : Set G) ≤ centralizer (A : Set G)) →
      A ≤ L ⊔ (M ⊓ centralizer (V : Set G)) := by
  intro A hAM hA hQ
  have hAV : A ≤ normalizer (V : Set G) := hAM.trans hMV
  have hrho : ∀ (a : ↥A) (v : ↥V),
      d.rho A hAV a (d.eqv v) = d.eqv (conjOn V a.1 (hAV a.2) v) :=
    fun a v => d.rho_eqv A hAV a v
  have hH2 : ∀ a : ↥A, a * a = 1 := fun a => Subtype.ext (by simpa [pow_two] using hA.2 a.1 a.2)
  have hadd : ∀ (a : ↥A) (x y : Fin 4 → d.F),
      d.rho A hAV a (x + y) = d.rho A hAV a x + d.rho A hAV a y :=
    fun a x y => d.act_add a.1 (hAV a.2) x y
  have hN : ∀ a : ↥A, ∀ g ∈ StatedSU 4 (2 ^ n) d.F, ∃ g' ∈ StatedSU 4 (2 ^ n) d.F,
      ∀ x : Fin 4 → d.F,
        d.rho A hAV a⁻¹ (((g : GL (Fin 4) d.F) : Matrix (Fin 4) (Fin 4) d.F) *ᵥ x) =
          ((g' : GL (Fin 4) d.F) : Matrix (Fin 4) (Fin 4) d.F) *ᵥ d.rho A hAV a⁻¹ x :=
    fun a g hg => d.act_normalizes hLM hML hMV (m := (a : G)⁻¹) (inv_mem (hAM a.2)) g hg
  have hQ' : ∀ K : Subgroup ↥A, K.index < Nat.card d.F → ∀ x : Fin 4 → d.F,
      (∀ k ∈ K, d.rho A hAV k x = x) → ∀ h : ↥A, d.rho A hAV h x = x := by
    intro K hK x hx h
    obtain ⟨v, rfl⟩ := d.eqv.surjective x
    have hBA : K.map A.subtype ≤ A := Subgroup.map_subtype_le K
    have hBidx : (K.map A.subtype).relIndex A = K.index := by
      rw [Subgroup.relIndex]
      exact congrArg Subgroup.index (Subgroup.comap_map_eq_self_of_injective A.subtype_injective K)
    have h2n : Nat.card d.F = 2 ^ (2 * n) := by rw [d.card_F, ← pow_mul, mul_comm]
    have hvC : (v : G) ∈ V ⊓ centralizer ((K.map A.subtype : Subgroup G) : Set G) := by
      refine ⟨v.2, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hb
      have h1 := hx k hk
      rw [hrho] at h1
      have h2 : (conjOn V k.1 (hAV k.2) v : ↥V) = v := d.eqv.injective h1
      have h3 : (k : G) * v * (k : G)⁻¹ = v := congrArg Subtype.val h2
      show (k : G) * v = v * k
      calc (k : G) * v = ((k : G) * v * (k : G)⁻¹) * k := by group
        _ = v * k := by rw [h3]
    have hvA := hQ (K.map A.subtype) hBA (by rw [hBidx, ← h2n]; exact hK) hvC
    have hcomm : (h : G) * v = v * h := Subgroup.mem_centralizer_iff.mp hvA h.1 h.2
    rw [hrho]
    exact congrArg d.eqv (Subtype.ext (by
      show (h : G) * v * (h : G)⁻¹ = v
      rw [hcomm]; group))
  have hmodel := model_Q d.card_F hn hH2 (d.rho A hAV) hadd hN hQ'
  intro a ha
  obtain ⟨g, hgS, hg⟩ := hmodel ⟨a, ha⟩
  obtain ⟨l, hl⟩ := d.ε_surj ⟨g, hgS⟩
  have hlL : (l : G) ∈ L := l.2
  have hlM : (l : G) ∈ M := hLM hlL
  have hlV : (l : G) ∈ normalizer (V : Set G) := hMV hlM
  have hgl : ((d.ε l : ↥(StatedSU 4 (2 ^ n) d.F)) : GL (Fin 4) d.F) = g := congrArg Subtype.val hl
  have hsame : ∀ v : ↥V, conjOn V a (hAV ha) v = conjOn V l hlV v := by
    intro v
    apply d.eqv.injective
    have h1 := hg (d.eqv v)
    rw [hrho, ← hgl] at h1
    exact h1.trans (d.eps_eqv hlL hlV v)
  have hcM : (l : G)⁻¹ * a ∈ M := M.mul_mem (M.inv_mem hlM) (hAM ha)
  have hcC : (l : G)⁻¹ * a ∈ centralizer (V : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have h1 : a * v * a⁻¹ = (l : G) * v * (l : G)⁻¹ := congrArg Subtype.val (hsame ⟨v, hv⟩)
    calc v * ((l : G)⁻¹ * a) = (l : G)⁻¹ * ((l : G) * v * (l : G)⁻¹) * a := by group
      _ = (l : G)⁻¹ * (a * v * a⁻¹) * a := by rw [h1]
      _ = ((l : G)⁻¹ * a) * v := by group
  have hmem : a = (l : G) * ((l : G)⁻¹ * a) := by group
  rw [hmem]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlL) (Subgroup.mem_sup_right ⟨hcM, hcC⟩)

end Facts

end CFSG.LocalAnalysis.RankThreeUC
