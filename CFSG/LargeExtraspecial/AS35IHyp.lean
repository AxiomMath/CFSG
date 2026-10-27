module

public import CFSG.LargeExtraspecial.AS35DHDefs
public import CFSG.LargeExtraspecial.AS35DMinNormal

public section

namespace CFSG.LargeExtraspecial.Asc22

open Subgroup Asc77

variable {G : Type} [Group G]

structure Hyp (N U P : Subgroup G) (z : G) : Prop where
  UN : U ≤ N
  PN : P ≤ N
  Ucen : ∀ u ∈ U, ∀ n ∈ N, u * n = n * u
  Usq : ∀ u ∈ U, u * u = 1
  UP : U ⊓ P = ⊥
  ext : IsExtraspecialPGroup 2 P
  zP : z ∈ P
  ZP : ∀ x ∈ P, (∀ y ∈ P, x * y = y * x) → x = 1 ∨ x = z
  Qnorm : ∀ c ∈ N, c * z = z * c → ∀ q ∈ U ⊔ P, c * q * c⁻¹ ∈ U ⊔ P
  syl : ∃ T : Sylow 2 N, ∀ t ∈ (T : Subgroup N), (t : G) * z = z * t
  zO : z ∈ (CFSG.pCore 2 N).map N.subtype
  notcen : ¬ N ≤ centralizer ({z} : Set G)
  max : ∀ H : Subgroup G, U ⊔ P ≤ H → H ≤ N → H ≠ N → H ≤ centralizer ({z} : Set G)
  gen : N ≤ closure {x | ∃ n ∈ N, ∃ q ∈ U ⊔ P, n * q * n⁻¹ = x}

abbrev cenM (N : Subgroup G) (z : G) : Subgroup G := N ⊓ centralizer ({z} : Set G)

abbrev genV (N : Subgroup G) (z : G) : Subgroup G := closure (conjIn z N)

abbrev kerV (N : Subgroup G) (z : G) : Subgroup G := N ⊓ centralizer (genV N z : Set G)

abbrev coreO (N : Subgroup G) : Subgroup G := (CFSG.pCore 2 N).map N.subtype

theorem mem_sup_of_commute {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} :
    x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  constructor
  · intro hx
    let S : Subgroup G :=
      { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
        mul_mem' := by
          rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
          refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
          calc a * b * (a' * b') = a * (b * a') * b' := by group
            _ = a * (a' * b) * b' := by rw [← hAB a' ha' b hb]
            _ = a * a' * (b * b') := by group
        one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by group⟩
        inv_mem' := by
          rintro _ ⟨a, ha, b, hb, rfl⟩
          refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
          have h1 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
            have := hAB a ha b hb
            calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
              _ = (a * b)⁻¹ := by rw [this]
              _ = b⁻¹ * a⁻¹ := by group
          rw [h1]; group }
    have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by group⟩)
      (fun b hb => ⟨1, A.one_mem, b, hb, by group⟩)
    exact hle hx
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)

theorem comm_of_mem_closure {S : Set G} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {a b : G}
    (ha : a ∈ closure S) (hb : b ∈ closure S) : a * b = b * a := by
  have h1 : closure S ≤ centralizer (closure S : Set G) := by
    rw [centralizer_closure]
    exact (closure_le _).2 fun x hx => mem_centralizer_iff.2 fun y hy => hS y hy x hx
  exact (mem_centralizer_iff.1 (h1 hb) a ha)

namespace Hyp

variable {N U P : Subgroup G} {z : G} (h : Hyp N U P z)
include h

theorem z_mem_center : (⟨z, h.zP⟩ : P) ∈ center P := by
  obtain ⟨c, hc1⟩ : ∃ c : center P, c ≠ 1 := by
    have h2 := h.ext.2.2.2
    by_contra hcon
    push Not at hcon
    have : Subsingleton (center P) := ⟨fun a b => (hcon a).trans (hcon b).symm⟩
    rw [Nat.card_unique] at h2
    omega
  have hcz : ((c : P) : G) = z := by
    rcases h.ZP ((c : P) : G) (c : P).2 fun y hy => by
        have := mem_center_iff.1 c.2 ⟨y, hy⟩
        exact congrArg Subtype.val this.symm with h1 | h1
    · exact absurd (Subtype.ext (Subtype.ext h1)) hc1
    · exact h1
  have : (⟨z, h.zP⟩ : P) = (c : P) := Subtype.ext hcz.symm
  rw [this]
  exact c.2

theorem z_comm_P {y : G} (hy : y ∈ P) : z * y = y * z := by
  have := mem_center_iff.1 h.z_mem_center ⟨y, hy⟩
  exact (congrArg Subtype.val this).symm

theorem z_ne_one : z ≠ 1 := by
  intro hz
  have h2 := h.ext.2.2.2
  have : center P = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rcases h.ZP (c : G) c.2 fun y hy => by
        have := mem_center_iff.1 hc ⟨y, hy⟩
        exact congrArg Subtype.val this.symm with h1 | h1
    · exact (mem_bot).2 (Subtype.ext h1)
    · exact (mem_bot).2 (Subtype.ext (h1.trans hz))
  rw [this, card_bot] at h2
  omega

theorem z_mul_self : z * z = 1 := by
  have h2 := h.ext.2.2.2
  have hpow := pow_card_eq_one' (G := center P) (x := ⟨⟨z, h.zP⟩, h.z_mem_center⟩)
  rw [h2] at hpow
  have := congrArg (fun x : center P => ((x : P) : G)) hpow
  simpa [pow_two] using this

theorem orderOf_z : orderOf z = 2 :=
  orderOf_eq_prime (by rw [pow_two, h.z_mul_self]) h.z_ne_one

theorem z_mem_N : z ∈ N := h.PN h.zP

theorem mem_sup {x : G} : x ∈ U ⊔ P ↔ ∃ u ∈ U, ∃ p ∈ P, x = u * p :=
  mem_sup_of_commute fun u hu p hp => h.Ucen u hu p (h.PN hp)

theorem sup_le_N : U ⊔ P ≤ N := sup_le h.UN h.PN

theorem comm_sup {x : G} (hx : x ∈ U ⊔ P) : x * z = z * x := by
  obtain ⟨u, hu, p, hp, rfl⟩ := h.mem_sup.1 hx
  calc u * p * z = u * (z * p) := by rw [mul_assoc, ← h.z_comm_P hp]
    _ = z * (u * p) := by rw [← mul_assoc, h.Ucen u hu z h.z_mem_N, mul_assoc]

theorem sup_le_M : U ⊔ P ≤ cenM N z := fun _ hx =>
  mem_inf.2 ⟨h.sup_le_N hx, mem_centralizer_singleton_iff.2 (h.comm_sup hx)⟩

theorem isPGroup_sup : IsPGroup 2 ↥(U ⊔ P) := by
  intro x
  obtain ⟨u, hu, p, hp, hx⟩ := h.mem_sup.1 x.2
  obtain ⟨k, hk⟩ := h.ext.1 ⟨p, hp⟩
  have hpk : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k + 1, Subtype.ext ?_⟩
  have hcomm : Commute u p := h.Ucen u hu p (h.PN hp)
  have hu2 : u ^ 2 = 1 := by rw [pow_two, h.Usq u hu]
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, hx]
  rw [hcomm.mul_pow, pow_succ, pow_mul, pow_mul, hpk, one_pow, mul_one, ← pow_mul, mul_comm,
    pow_mul, hu2, one_pow]

theorem exists_of_central {x : G} (hx : x ∈ U ⊔ P) (hc : ∀ y ∈ U ⊔ P, x * y = y * x) :
    ∃ u ∈ U, x = u ∨ x = u * z := by
  obtain ⟨u, hu, p, hp, rfl⟩ := h.mem_sup.1 hx
  have hpc : ∀ y ∈ P, p * y = y * p := by
    intro y hy
    have h1 := hc y (mem_sup_right hy)
    have h2 := h.Ucen u hu y (h.PN hy)
    have : u * (p * y) = u * (y * p) := by
      calc u * (p * y) = u * p * y := by group
        _ = y * (u * p) := h1
        _ = (y * u) * p := by group
        _ = (u * y) * p := by rw [h2]
        _ = u * (y * p) := by group
    exact mul_left_cancel this
  rcases h.ZP p hp hpc with h1 | h1
  · exact ⟨u, hu, Or.inl (by rw [h1, mul_one])⟩
  · exact ⟨u, hu, Or.inr (by rw [h1])⟩

theorem mem_M_of_normalizes {g : G} (hg : g ∈ N)
    (hgM : ∀ m, m ∈ cenM N z ↔ g * m * g⁻¹ ∈ cenM N z) : g ∈ cenM N z := by
  set H := N ⊓ normalizer (cenM N z : Set G) with hHdef
  have hQH : U ⊔ P ≤ H := fun q hq => mem_inf.2 ⟨h.sup_le_N hq, le_normalizer (h.sup_le_M hq)⟩
  by_cases hH : H = N
  · exfalso
    apply h.notcen
    refine h.gen.trans ((closure_le _).2 ?_)
    rintro _ ⟨n, hn, q, hq, rfl⟩
    have hnH : n ∈ H := hH ▸ hn
    exact (mem_inf.1 ((mem_normalizer_iff.1 (mem_inf.1 hnH).2 q).1 (h.sup_le_M hq))).2
  · exact mem_inf.2 ⟨hg, h.max H hQH inf_le_left hH (mem_inf.2 ⟨hg, mem_normalizer_iff.2 hgM⟩)⟩

theorem mem_M_of_conj_le [Finite G] {g : G} (hg : g ∈ N)
    (hQ : ∀ q ∈ U ⊔ P, g * q * g⁻¹ ∈ cenM N z) : g ∈ cenM N z := by
  set H : Subgroup G := (cenM N z).map (MulAut.conj g⁻¹).toMonoidHom with hHdef
  have hmemH : ∀ x, x ∈ H ↔ g * x * g⁻¹ ∈ cenM N z := by
    intro x
    constructor
    · rintro ⟨m, hm, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hm
    · intro hx
      exact ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩
  have hQH : U ⊔ P ≤ H := fun q hq => (hmemH q).2 (hQ q hq)
  have hHN : H ≤ N := by
    intro x hx
    have h1 := (mem_inf.1 ((hmemH x).1 hx)).1
    rw [show x = g⁻¹ * (g * x * g⁻¹) * g by group]
    exact N.mul_mem (N.mul_mem (N.inv_mem hg) h1) hg
  have hHne : H ≠ N := by
    intro hHN'
    apply h.notcen
    intro n hn
    have hn' : g⁻¹ * n * g ∈ H := hHN' ▸ N.mul_mem (N.mul_mem (N.inv_mem hg) hn) hg
    have h1 := (hmemH _).1 hn'
    rw [show g * (g⁻¹ * n * g) * g⁻¹ = n by group] at h1
    exact (mem_inf.1 h1).2
  have hHM : H ≤ cenM N z := fun x hx => mem_inf.2 ⟨hHN hx, h.max H hQH hHN hHne hx⟩
  have hcard : Nat.card H = Nat.card (cenM N z) :=
    card_map_of_injective (MulAut.conj g⁻¹).injective
  have hHeq : H = cenM N z := eq_of_le_of_card_ge hHM hcard.ge
  refine h.mem_M_of_normalizes hg fun m => ?_
  rw [← hmemH, hHeq]

theorem le_sup_conj [Finite G] {g : G} (hg : g ∈ N) (hgM : g ∉ cenM N z) :
    N ≤ (U ⊔ P) ⊔ (U ⊔ P).map (MulAut.conj g).toMonoidHom := by
  have hconj : ∀ q ∈ U ⊔ P, g * q * g⁻¹ ∈ N := fun q hq =>
    N.mul_mem (N.mul_mem hg (h.sup_le_N hq)) (N.inv_mem hg)
  set H := (U ⊔ P) ⊔ (U ⊔ P).map (MulAut.conj g).toMonoidHom with hHdef
  have hHN : H ≤ N := sup_le h.sup_le_N (by
    rintro _ ⟨q, hq, rfl⟩
    exact hconj q hq)
  by_contra hNH
  have hne : H ≠ N := fun e => hNH (e ▸ le_rfl)
  have hcen := h.max H le_sup_left hHN hne
  exact hgM (h.mem_M_of_conj_le hg fun q hq =>
    mem_inf.2 ⟨hconj q hq, hcen (mem_sup_right ⟨q, hq, rfl⟩)⟩)

omit h in
theorem coreO_normalized {n x : G} (hn : n ∈ N) (hx : x ∈ coreO N) : n * x * n⁻¹ ∈ coreO N := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨n, hn⟩ * y * ⟨n, hn⟩⁻¹, CFSG.pCore_normal.conj_mem y hy _, rfl⟩

theorem coreO_le_cen [Finite G] : coreO N ≤ centralizer ({z} : Set G) := by
  obtain ⟨T, hT⟩ := h.syl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CFSG.pCore 2 N).Normal := CFSG.pCore_normal
  have hle : CFSG.pCore 2 N ≤ (T : Subgroup N) :=
    IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup T
  rintro _ ⟨y, hy, rfl⟩
  exact mem_centralizer_singleton_iff.2 (hT y (hle hy))

theorem conjIn_subset_coreO : conjIn z N ⊆ coreO N := by
  rintro _ ⟨n, hn, rfl⟩
  exact coreO_normalized hn h.zO

theorem comm_conjIn [Finite G] {a b : G} (ha : a ∈ conjIn z N) (hb : b ∈ conjIn z N) :
    a * b = b * a := by
  obtain ⟨n, hn, rfl⟩ := ha
  have hb' : n⁻¹ * b * n ∈ coreO N := by
    simpa using coreO_normalized (N.inv_mem hn) (h.conjIn_subset_coreO hb)
  have hc := mem_centralizer_singleton_iff.1 (h.coreO_le_cen hb')
  calc n * z * n⁻¹ * b = n * (z * (n⁻¹ * b * n)) * n⁻¹ := by group
    _ = n * (n⁻¹ * b * n * z) * n⁻¹ := by rw [hc]
    _ = b * (n * z * n⁻¹) := by group

theorem comm_V [Finite G] {a b : G} (ha : a ∈ genV N z) (hb : b ∈ genV N z) : a * b = b * a :=
  comm_of_mem_closure (fun _ ha _ hb => h.comm_conjIn ha hb) ha hb

theorem mul_self_V [Finite G] {v : G} (hv : v ∈ genV N z) : v * v = 1 := by
  induction hv using closure_induction with
  | mem x hx =>
    obtain ⟨n, hn, rfl⟩ := hx
    calc n * z * n⁻¹ * (n * z * n⁻¹) = n * (z * z) * n⁻¹ := by group
      _ = 1 := by rw [h.z_mul_self]; group
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxy := h.comm_V hx hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy]
      _ = x * x * (y * y) := by group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x _ ih => rw [← mul_inv_rev, ih, inv_one]

theorem inv_V [Finite G] {v : G} (hv : v ∈ genV N z) : v⁻¹ = v :=
  inv_eq_of_mul_eq_one_right (h.mul_self_V hv)

omit h in
theorem z_mem_V : z ∈ genV N z := subset_closure (self_mem_conjIn z N)

theorem genV_le_coreO : genV N z ≤ coreO N := (closure_le _).2 h.conjIn_subset_coreO

theorem genV_le_N : genV N z ≤ N := h.genV_le_coreO.trans (map_subtype_le _)

theorem genV_le_M [Finite G] : genV N z ≤ cenM N z := fun _ hv =>
  mem_inf.2 ⟨h.genV_le_N hv, h.coreO_le_cen (h.genV_le_coreO hv)⟩

omit h in
theorem conj_mem_genV {n v : G} (hn : n ∈ N) (hv : v ∈ genV N z) : n * v * n⁻¹ ∈ genV N z := by
  induction hv using closure_induction with
  | mem x hx => exact subset_closure (conj_mem_conjIn_of_mem hn hx)
  | one => simp
  | mul x y _ _ ihx ihy =>
    have := mul_mem ihx ihy
    rwa [show n * x * n⁻¹ * (n * y * n⁻¹) = n * (x * y) * n⁻¹ by group] at this
  | inv x _ ih =>
    have := inv_mem ih
    rwa [show (n * x * n⁻¹)⁻¹ = n * x⁻¹ * n⁻¹ by group] at this

omit h in
theorem conjIn_subset_genV : conjIn z N ⊆ genV N z := subset_closure

omit h in
theorem kerV_le_M : kerV N z ≤ cenM N z := fun _ hk =>
  mem_inf.2 ⟨(mem_inf.1 hk).1, mem_centralizer_singleton_iff.2
    ((mem_centralizer_iff.1 (mem_inf.1 hk).2 z z_mem_V).symm)⟩

theorem z_mem_kerV [Finite G] : z ∈ kerV N z :=
  mem_inf.2 ⟨h.z_mem_N, mem_centralizer_iff.2 fun _ hv => h.comm_V hv z_mem_V⟩

theorem U_le_kerV : U ≤ kerV N z := fun u hu =>
  mem_inf.2 ⟨h.UN hu, mem_centralizer_iff.2 fun v hv => (h.Ucen u hu v (h.genV_le_N hv)).symm⟩

omit h in
theorem kerV_normalized {n k : G} (hn : n ∈ N) (hk : k ∈ kerV N z) :
    n * k * n⁻¹ ∈ kerV N z := by
  refine mem_inf.2 ⟨N.mul_mem (N.mul_mem hn (mem_inf.1 hk).1) (N.inv_mem hn),
    mem_centralizer_iff.2 fun v hv => ?_⟩
  have hv' : n⁻¹ * v * n ∈ genV N z := by simpa using conj_mem_genV (N.inv_mem hn) hv
  have hc := mem_centralizer_iff.1 (mem_inf.1 hk).2 _ hv'
  calc v * (n * k * n⁻¹) = n * ((n⁻¹ * v * n) * k) * n⁻¹ := by group
    _ = n * (k * (n⁻¹ * v * n)) * n⁻¹ := by rw [hc]
    _ = n * k * n⁻¹ * v := by group

omit h in
theorem le_kerV {X : Subgroup G} (hXM : X ≤ cenM N z)
    (hXn : ∀ n ∈ N, ∀ x ∈ X, n * x * n⁻¹ ∈ X) : X ≤ kerV N z := by
  intro x hx
  refine mem_inf.2 ⟨(mem_inf.1 (hXM hx)).1, ?_⟩
  rw [centralizer_closure, mem_centralizer_iff]
  rintro _ ⟨n, hn, rfl⟩
  have h1 : n⁻¹ * x * n ∈ X := by simpa using hXn n⁻¹ (N.inv_mem hn) x hx
  have h2 := mem_centralizer_singleton_iff.1 (mem_inf.1 (hXM h1)).2
  calc n * z * n⁻¹ * x = n * (z * (n⁻¹ * x * n)) * n⁻¹ := by group
    _ = n * (n⁻¹ * x * n * z) * n⁻¹ := by rw [h2]
    _ = x * (n * z * n⁻¹) := by group

omit h in
theorem mem_kerV_iff {k : G} (hk : k ∈ N) :
    k ∈ kerV N z ↔ ∀ t ∈ conjIn z N, t * k = k * t := by
  rw [kerV, mem_inf, centralizer_closure, mem_centralizer_iff]
  exact ⟨fun h' => h'.2, fun h' => ⟨hk, h'⟩⟩

theorem inf_le_centerIn : U ⊓ genV N z ≤ Asc77.centerIn z N := fun u hu =>
  mem_inf.2 ⟨(mem_inf.1 hu).2, mem_centralizer_iff.2 fun n hn =>
    (h.Ucen u (mem_inf.1 hu).1 n hn).symm⟩

theorem z_not_mem_centerIn : z ∉ Asc77.centerIn z N := fun hz =>
  h.notcen fun n hn => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (mem_inf.1 hz).2 n hn)

theorem commutator_le_inf [Finite G] : ⁅genV N z, U ⊔ P⁆ ≤ (U ⊔ P) ⊓ genV N z := by
  rw [commutator_le]
  intro v hv q hq
  rw [commutatorElement_def]
  refine mem_inf.2 ⟨?_, ?_⟩
  · have hvM := h.genV_le_M hv
    exact mul_mem (h.Qnorm v (mem_inf.1 hvM).1 (mem_centralizer_singleton_iff.1 (mem_inf.1 hvM).2)
      q hq) (inv_mem hq)
  · rw [show v * q * v⁻¹ * q⁻¹ = v * (q * v⁻¹ * q⁻¹) by group]
    exact mul_mem hv (conj_mem_genV (h.sup_le_N hq) (inv_mem hv))

end Hyp

end CFSG.LargeExtraspecial.Asc22
