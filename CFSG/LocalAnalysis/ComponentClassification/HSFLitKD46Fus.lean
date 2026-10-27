module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46TE

public section

namespace CFSG.ComponentClassification.HSFLit.KD46

open CFSG Subgroup Equiv L2K L2KD

theorem comm_center_pTE : ∀ (u : (ZMod 8)ˣ) (b : ZMod 8) (s e : ZMod 8), dbit8 b = 0 →
    (s = 2 ∨ s = 6) → dbit8 e = 0 → aff8 u b * aff8 1 s = aff8 1 s * aff8 u b →
    aff8 u b * aff8 (-1) e = aff8 (-1) e * aff8 u b → pB u b := by
  intro u b s e
  simp only [aff8_mul, aff8_eq_iff]
  revert u b s e
  decide

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} (S : KDBase A C)

theorem normalizer_T_le : normalizer (A.T : Set X) ≤ normalizer (S.TE : Set X) := fun _ hw =>
  mem_normalizer_TE_of_conj_le S fun a ha => (mem_normalizer_iff.mp hw a).mp (TE_le_T S ha)

theorem T_le_normalizer_TE : A.T ≤ normalizer (S.TE : Set X) := fun _ hg =>
  mem_normalizer_of_conj_mem fun _ ha => conj_mem_TE S hg ha

theorem x_mem_TE : S.x ∈ S.TE := by
  rw [mem_TE_iff]
  refine ⟨x_mem_T S, ?_⟩
  rcases ψ_x S with h | h <;> rw [h, mem_PTE] <;> decide

theorem y_mem_TE : S.y ∈ S.TE := E_le_TE S S.y_mem (mem_E_yi S _)

theorem mem_B_of_comm {g : X} (hg : g ∈ S.TE) (hx : g * S.x = S.x * g) (hy : g * S.y = S.y * g) :
    g ∈ S.B := by
  obtain ⟨hgT, ⟨u, b, hub, hb⟩⟩ := (mem_TE_iff S).mp hg
  rw [mem_B_iff]
  refine ⟨hgT, ?_⟩
  obtain ⟨e, he, hψy⟩ := ψ_y S
  have hcx := congrArg (ψX A) hx
  have hcy := congrArg (ψX A) hy
  rw [ψX_mul hgT (x_mem_T S), ψX_mul (x_mem_T S) hgT, ← hub] at hcx
  rw [ψX_mul hgT (y_mem_T S), ψX_mul (y_mem_T S) hgT, ← hub, hψy] at hcy
  rw [← hub, mem_PB]
  rcases ψ_x S with h | h <;> rw [h] at hcx
  · exact comm_center_pTE u b 2 e hb (Or.inl rfl) he hcx hcy
  · exact comm_center_pTE u b 6 e hb (Or.inr rfl) he hcx hcy

theorem conj_mem_B_of_mem_normalizer {n b : X} (hn : n ∈ normalizer (S.TE : Set X))
    (hb : b ∈ S.B) : n * b * n⁻¹ ∈ S.B := by
  have hbE : n * b * n⁻¹ ∈ S.TE := (mem_normalizer_iff.mp hn b).mp (B_le_TE S hb)
  have hcomm : ∀ a ∈ S.TE, n * b * n⁻¹ * a = a * (n * b * n⁻¹) := by
    intro a ha
    have ha' : n⁻¹ * a * n ∈ S.TE := by
      have := (mem_normalizer_iff.mp (inv_mem hn) a).mp ha
      rwa [inv_inv] at this
    have hc := comm_B_TE S hb ha'
    calc n * b * n⁻¹ * a = n * (b * (n⁻¹ * a * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * a * n) * b) * n⁻¹ := by rw [hc]
      _ = a * (n * b * n⁻¹) := by group
  exact mem_B_of_comm S hbE (hcomm _ (x_mem_TE S)) (hcomm _ (y_mem_TE S))

theorem sq_of_mem_TE {g : X} (hg : g ∈ S.TE) : g ^ 2 = 1 ∨ g ^ 2 = S.z := by
  obtain ⟨hgT, ⟨u, b, hub, hb⟩⟩ := (mem_TE_iff S).mp hg
  obtain ⟨r, hr, a, e, -, -, rfl, -⟩ := exists_eq_of_mem_T C hgT hub.symm hb
  have hrt : Commute r (t ^ a) := (Commute.pow_right (comm_t hr.1) a)
  have hrk : Commute r (C.k ^ e) := (Commute.pow_right (k_comm_R S hr).symm e)
  have htk : Commute (t ^ a) (C.k ^ e) := (Commute.pow_pow (k_comm_t S).symm a e)
  have hw : Commute r (t ^ a * C.k ^ e) := hrt.mul_right hrk
  have hw2 : (t ^ a * C.k ^ e) ^ 2 = 1 := by
    rw [htk.mul_pow, ← pow_mul, ← pow_mul, mul_comm a 2, mul_comm e 2, pow_mul, pow_mul,
      t_sq' (A := A), show C.k ^ 2 = 1 from k_sq S, one_pow, one_pow, mul_one]
  have h1 : (r * t ^ a * C.k ^ e) ^ 2 = r ^ 2 := by rw [mul_assoc, hw.mul_pow, hw2, mul_one]
  rw [h1]
  rcases sq_mem_R8 (ψX_mem_R8 hr) with h | h
  · exact Or.inl (eq_one_of_ψX (pow_mem hr 2) (by rw [ψX_pow hr.1, h]))
  · exact Or.inr (eq_of_ψX_eq (pow_mem hr 2) (z_mem S) (by rw [ψX_pow hr.1, h, ψ_z]))

theorem conj_z_of_mem_normalizer {n : X} (hn : n ∈ normalizer (S.TE : Set X)) :
    n * S.z * n⁻¹ = S.z := by
  have hx : n * S.x * n⁻¹ ∈ S.TE := (mem_normalizer_iff.mp hn _).mp (x_mem_TE S)
  have e : n * S.z * n⁻¹ = (n * S.x * n⁻¹) ^ 2 := by rw [conj_pow]; rfl
  rcases sq_of_mem_TE S hx with h | h
  · exfalso
    apply z_ne_one S
    calc S.z = n⁻¹ * (n * S.z * n⁻¹) * n := by group
      _ = 1 := by rw [e, h]; group
  · rw [e, h]

theorem exists_normalizer_conj_eq {b : X} (hb : b ∈ S.B) (hconj : ConjTo t b) :
    ∃ n ∈ normalizer (S.TE : Set X), n * t * n⁻¹ = b := by
  obtain ⟨g, rfl⟩ := hconj
  set P : Subgroup X := S.TE.map (MulAut.conj g⁻¹).toMonoidHom with hP
  have hPp : IsPGroup 2 P := (A.isPGroup_T.to_le (TE_le_T S)).map _
  have hPC : P ≤ centralizer ({t} : Set X) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have := comm_B_TE S hb ha
    calc g⁻¹ * a * g * t = g⁻¹ * (a * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * a) * g := by rw [this]
      _ = t * (g⁻¹ * a * g) := by group
  obtain ⟨c, hc, hcT⟩ := exists_conj_le_T (A := A) hPp hPC
  have hN : c * g⁻¹ ∈ normalizer (S.TE : Set X) := by
    refine mem_normalizer_TE_of_conj_le S fun a ha => ?_
    have : c * (g⁻¹ * a * g⁻¹⁻¹) * c⁻¹ ∈ A.T := hcT ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    simpa [mul_assoc] using this
  refine ⟨(c * g⁻¹)⁻¹, inv_mem hN, ?_⟩
  have hct : c⁻¹ * t * c = t := by
    rw [mem_centralizer_singleton_iff.mp (inv_mem hc)]
    group
  calc (c * g⁻¹)⁻¹ * t * (c * g⁻¹)⁻¹⁻¹ = g * (c⁻¹ * t * c) * g⁻¹ := by group
    _ = g * t * g⁻¹ := by rw [hct]

theorem not_conjTo_z : ¬ ConjTo t S.z := by
  intro h
  obtain ⟨n, hn, hnt⟩ := exists_normalizer_conj_eq S (mem_B_z S) h
  have h1 := conj_z_of_mem_normalizer S (inv_mem hn)
  have : t = S.z := by
    calc t = n⁻¹ * (n * t * n⁻¹) * n⁻¹⁻¹ := by group
      _ = S.z := by rw [hnt, h1]
  exact A.config.not_mem (this ▸ (z_mem S).2)

theorem exists_normalizer_E_conj_eq {yi : X} (hyi : yi = S.y ∨ yi = S.x * S.y) {e : X}
    (he : e ∈ S.E yi) (hconj : ConjTo t e) :
    ∃ n ∈ normalizer (S.E yi : Set X), n * t * n⁻¹ = e := by
  have hyiR : yi ∈ A.R := by rcases hyi with rfl | rfl; exacts [S.y_mem, xy_mem S]
  have hyi2 : yi ^ 2 = 1 := by rcases hyi with rfl | rfl; exacts [S.y_sq, xy_sq S]
  have hyiB : yi ∉ S.B := by rcases hyi with rfl | rfl; exacts [y_not_mem_B S, xy_not_mem_B S]
  obtain ⟨g, rfl⟩ := hconj
  set P : Subgroup X := (S.E yi).map (MulAut.conj g⁻¹).toMonoidHom with hP
  have hPp : IsPGroup 2 P := (A.isPGroup_T.to_le (E_le_T S yi hyiR)).map _
  have hPC : P ≤ centralizer ({t} : Set X) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have := E_comm S hyiR ha he
    calc g⁻¹ * a * g * t = g⁻¹ * (a * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * a) * g := by rw [this]
      _ = t * (g⁻¹ * a * g) := by group
  obtain ⟨c, hc, hcT⟩ := exists_conj_le_T (A := A) hPp hPC
  set m := c * g⁻¹ with hm
  have hmap : (S.E yi).map (MulAut.conj m).toMonoidHom ≤ A.T := by
    rintro _ ⟨a, ha, rfl⟩
    have : c * (g⁻¹ * a * g⁻¹⁻¹) * c⁻¹ ∈ A.T := hcT ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    simpa [hm, mul_assoc] using this
  have hcases := eq_E_of_card S hmap (elem_map (elem_E S hyiR hyi2) m)
    (by rw [card_map_of_injective (MulAut.conj m).injective, card_E S hyiR hyi2 hyiB])
  have hmem : ∀ {E' : Subgroup X}, (S.E yi).map (MulAut.conj m).toMonoidHom = E' →
      ∀ a ∈ S.E yi, m * a * m⁻¹ ∈ E' := by
    intro E' hE' a ha
    rw [← hE']
    exact ⟨a, ha, rfl⟩
  have hmt : m⁻¹ * t * m = g * t * g⁻¹ := by
    have h1 : c⁻¹ * t * c = t := by
      rw [mem_centralizer_singleton_iff.mp (inv_mem hc)]
      group
    calc m⁻¹ * t * m = g * (c⁻¹ * t * c) * g⁻¹ := by rw [hm]; group
      _ = g * t * g⁻¹ := by rw [h1]
  have hdt : S.d⁻¹ * t * S.d = t := by
    rw [mem_centralizer_singleton_iff.mp (inv_mem (A.T_le_centralizer (d_mem_T S)))]
    group
  have hd := fun {a : X} => conj_E_of_not_mem_TE S (e := a) (d_mem_T S) (d_not_mem_TE S)
  have hfin : (∀ a ∈ S.E yi, m * a * m⁻¹ ∈ S.E yi) ∨
      (∀ a ∈ S.E yi, S.d * (m * a * m⁻¹) * S.d⁻¹ ∈ S.E yi) := by
    rcases hyi with rfl | rfl <;> rcases hcases with h | h
    · exact Or.inl (hmem h)
    · exact Or.inr fun a ha => (hd).2 (hmem h a ha)
    · exact Or.inr fun a ha => (hd).1 (hmem h a ha)
    · exact Or.inl (hmem h)
  rcases hfin with h | h
  · refine ⟨m⁻¹, inv_mem (mem_normalizer_of_conj_mem h), ?_⟩
    rw [inv_inv, hmt]
  · have hN : S.d * m ∈ normalizer (S.E yi : Set X) := mem_normalizer_of_conj_mem fun a ha => by
      have := h a ha
      simpa [mul_assoc] using this
    refine ⟨(S.d * m)⁻¹, inv_mem hN, ?_⟩
    calc (S.d * m)⁻¹ * t * (S.d * m)⁻¹⁻¹ = m⁻¹ * (S.d⁻¹ * t * S.d) * m := by group
      _ = g * t * g⁻¹ := by rw [hdt, hmt]

theorem eq_TE_of_le {yi : X} (hyi : yi = S.y ∨ yi = S.x * S.y) {Q : Subgroup X}
    (hQ : IsPGroup 2 Q) (hTQ : S.TE ≤ Q)
    (hQN : Q ≤ normalizer (S.E yi : Set X) ⊓ centralizer ({t} : Set X)) : Q = S.TE := by
  have hyiR : yi ∈ A.R := by rcases hyi with rfl | rfl; exacts [S.y_mem, xy_mem S]
  have hyi2 : yi ^ 2 = 1 := by rcases hyi with rfl | rfl; exacts [S.y_sq, xy_sq S]
  have hyiB : yi ∉ S.B := by rcases hyi with rfl | rfl; exacts [y_not_mem_B S, xy_not_mem_B S]
  obtain ⟨c, hc, hcT⟩ := exists_conj_le_T (A := A) hQ (hQN.trans inf_le_right)
  have hEQ : S.E yi ≤ Q := (E_le_TE S hyiR).trans hTQ
  have hmap : (S.E yi).map (MulAut.conj c).toMonoidHom ≤ A.T := fun a ha => by
    obtain ⟨b, hb, rfl⟩ := ha
    exact hcT ⟨b, hEQ hb, rfl⟩
  have hcases := eq_E_of_card S hmap (elem_map (elem_E S hyiR hyi2) c)
    (by rw [card_map_of_injective (MulAut.conj c).injective, card_E S hyiR hyi2 hyiB])
  have hle : Q.map (MulAut.conj c).toMonoidHom ≤ S.TE := by
    rintro _ ⟨q, hq, rfl⟩
    have hqT : c * q * c⁻¹ ∈ A.T := hcT ⟨q, hq, rfl⟩
    have hqN : q ∈ normalizer (S.E yi : Set X) := (mem_inf.mp (hQN hq)).1
    have hN : ∀ {E' : Subgroup X}, (S.E yi).map (MulAut.conj c).toMonoidHom = E' →
        c * q * c⁻¹ ∈ normalizer (E' : Set X) := by
      intro E' hE'
      refine mem_normalizer_of_conj_mem fun a ha => ?_
      rw [← hE'] at ha ⊢
      obtain ⟨b, hb, rfl⟩ := ha
      refine ⟨q * b * q⁻¹, (mem_normalizer_iff.mp hqN b).mp hb, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rcases hcases with h | h
    · exact mem_TE_of_mem_normalizer_E₁ S hqT (hN h)
    · exact mem_TE_of_mem_normalizer_E₂ S hqT (hN h)
  refine le_antisymm ?_ hTQ
  have hcard : Nat.card Q ≤ Nat.card S.TE := by
    have h1 : Nat.card (Q.map (MulAut.conj c).toMonoidHom) = Nat.card Q :=
      card_map_of_injective (MulAut.conj c).injective
    rw [← h1]
    exact card_le_of_le hle
  exact (eq_of_le_of_card_ge hTQ hcard).symm.le

theorem TE_le_normalizer_E {yi : X} (hyi : yi = S.y ∨ yi = S.x * S.y) :
    S.TE ≤ normalizer (S.E yi : Set X) := by
  rcases hyi with rfl | rfl
  · exact TE_le_normalizer_E₁ S
  · exact TE_le_normalizer_E₂ S

theorem card_TE_eq_two_pow {yi : X} (hyi : yi = S.y ∨ yi = S.x * S.y) :
    Nat.card S.TE =
      2 ^ (Nat.card (normalizer (S.E yi : Set X) ⊓ centralizer ({t} : Set X) :
        Subgroup X)).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (S.E yi : Set X) ⊓ centralizer ({t} : Set X) with hN
  have hTN : S.TE ≤ N := le_inf (TE_le_normalizer_E S hyi) ((TE_le_T S).trans A.T_le_centralizer)
  have hTp : IsPGroup 2 (S.TE.subgroupOf N) :=
    (A.isPGroup_T.to_le (TE_le_T S)).comap_of_injective _ (subtype_injective _)
  obtain ⟨P, hP⟩ := hTp.exists_le_sylow
  set Q : Subgroup X := (P : Subgroup N).map N.subtype with hQ
  have hQp : IsPGroup 2 Q := P.isPGroup'.map _
  have hTQ : S.TE ≤ Q := fun a ha => ⟨⟨a, hTN ha⟩, hP ha, rfl⟩
  have hQN : Q ≤ N := map_subtype_le _
  have heq := eq_TE_of_le S hyi hQp hTQ hQN
  rw [← heq, hQ, card_map_of_injective (subtype_injective _), Sylow.card_eq_multiplicity]

end CFSG.ComponentClassification.HSFLit.KD46
