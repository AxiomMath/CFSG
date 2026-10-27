module

public import CFSG.GH74.GLS.C3.Layer1.St1P89D8
public import CFSG.GH74.GLS.C3.Layer1.St1P89Z

public section

namespace CFSG.GH74.GLS.C3.Layer1.P89

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.Uniqueness.SU.SU1

namespace E16Aux

section General

variable {G : Type} [Group G]

structure Inv4 (a b c d : G) : Prop where
  ab : a * b = b * a
  ac : a * c = c * a
  ad : a * d = d * a
  bc : b * c = c * b
  bd : b * d = d * b
  cd : c * d = d * c
  a2 : a ^ 2 = 1
  b2 : b ^ 2 = 1
  c2 : c ^ 2 = 1
  d2 : d ^ 2 = 1

theorem prod4_mul {a b c d : G} (hab : a * b = b * a) (hac : a * c = c * a) (had : a * d = d * a)
    (hbc : b * c = c * b) (hbd : b * d = d * b) (hcd : c * d = d * c) (i j k l i' j' k' l' : ℕ) :
    a ^ i * b ^ j * c ^ k * d ^ l * (a ^ i' * b ^ j' * c ^ k' * d ^ l') =
      a ^ (i + i') * b ^ (j + j') * c ^ (k + k') * d ^ (l + l') := by
  have h1 : ∀ m n : ℕ, b ^ m * a ^ n = a ^ n * b ^ m := fun m n =>
    ((Commute.pow_pow (show Commute b a from hab.symm) m n)).eq
  have h2 : ∀ m n : ℕ, c ^ m * a ^ n = a ^ n * c ^ m := fun m n =>
    ((Commute.pow_pow (show Commute c a from hac.symm) m n)).eq
  have h3 : ∀ m n : ℕ, d ^ m * a ^ n = a ^ n * d ^ m := fun m n =>
    ((Commute.pow_pow (show Commute d a from had.symm) m n)).eq
  have h4 : ∀ m n : ℕ, c ^ m * b ^ n = b ^ n * c ^ m := fun m n =>
    ((Commute.pow_pow (show Commute c b from hbc.symm) m n)).eq
  have h5 : ∀ m n : ℕ, d ^ m * b ^ n = b ^ n * d ^ m := fun m n =>
    ((Commute.pow_pow (show Commute d b from hbd.symm) m n)).eq
  have h6 : ∀ m n : ℕ, d ^ m * c ^ n = c ^ n * d ^ m := fun m n =>
    ((Commute.pow_pow (show Commute d c from hcd.symm) m n)).eq
  rw [pow_add a i i', pow_add b j j', pow_add c k k', pow_add d l l']
  calc a ^ i * b ^ j * c ^ k * d ^ l * (a ^ i' * b ^ j' * c ^ k' * d ^ l')
      = a ^ i * b ^ j * c ^ k * (d ^ l * a ^ i') * b ^ j' * c ^ k' * d ^ l' := by group
    _ = a ^ i * b ^ j * c ^ k * (a ^ i' * d ^ l) * b ^ j' * c ^ k' * d ^ l' := by rw [h3]
    _ = a ^ i * b ^ j * (c ^ k * a ^ i') * d ^ l * b ^ j' * c ^ k' * d ^ l' := by group
    _ = a ^ i * b ^ j * (a ^ i' * c ^ k) * d ^ l * b ^ j' * c ^ k' * d ^ l' := by rw [h2]
    _ = a ^ i * (b ^ j * a ^ i') * c ^ k * d ^ l * b ^ j' * c ^ k' * d ^ l' := by group
    _ = a ^ i * (a ^ i' * b ^ j) * c ^ k * d ^ l * b ^ j' * c ^ k' * d ^ l' := by rw [h1]
    _ = a ^ i * a ^ i' * b ^ j * c ^ k * (d ^ l * b ^ j') * c ^ k' * d ^ l' := by group
    _ = a ^ i * a ^ i' * b ^ j * c ^ k * (b ^ j' * d ^ l) * c ^ k' * d ^ l' := by rw [h5]
    _ = a ^ i * a ^ i' * b ^ j * (c ^ k * b ^ j') * d ^ l * c ^ k' * d ^ l' := by group
    _ = a ^ i * a ^ i' * b ^ j * (b ^ j' * c ^ k) * d ^ l * c ^ k' * d ^ l' := by rw [h4]
    _ = a ^ i * a ^ i' * b ^ j * b ^ j' * c ^ k * (d ^ l * c ^ k') * d ^ l' := by group
    _ = a ^ i * a ^ i' * b ^ j * b ^ j' * c ^ k * (c ^ k' * d ^ l) * d ^ l' := by rw [h6]
    _ = a ^ i * a ^ i' * b ^ j * b ^ j' * c ^ k * c ^ k' * d ^ l * d ^ l' := by group
    _ = a ^ i * a ^ i' * (b ^ j * b ^ j') * (c ^ k * c ^ k') * (d ^ l * d ^ l') := by group

theorem Inv4.prod_mul {a b c d : G} (h : Inv4 a b c d) (i j k l i' j' k' l' : ℕ) :
    a ^ i * b ^ j * c ^ k * d ^ l * (a ^ i' * b ^ j' * c ^ k' * d ^ l') =
      a ^ (i + i') * b ^ (j + j') * c ^ (k + k') * d ^ (l + l') :=
  prod4_mul h.ab h.ac h.ad h.bc h.bd h.cd i j k l i' j' k' l'

theorem Inv4.prod_sq {a b c d : G} (h : Inv4 a b c d) (i j k l : ℕ) :
    (a ^ i * b ^ j * c ^ k * d ^ l) * (a ^ i * b ^ j * c ^ k * d ^ l) = 1 := by
  rw [h.prod_mul]
  have e : ∀ (y : G) (m : ℕ), y ^ 2 = 1 → y ^ (m + m) = 1 := fun y m hy => by
    rw [← two_mul, pow_mul, hy, one_pow]
  rw [e a i h.a2, e b j h.b2, e c k h.c2, e d l h.d2]
  simp

theorem Inv4.exists_mul {a b c d : G} (h : Inv4 a b c d) {g g' : G}
    (hg : ∃ i j k l : ℕ, g = a ^ i * b ^ j * c ^ k * d ^ l)
    (hg' : ∃ i j k l : ℕ, g' = a ^ i * b ^ j * c ^ k * d ^ l) :
    ∃ i j k l : ℕ, g * g' = a ^ i * b ^ j * c ^ k * d ^ l := by
  obtain ⟨i, j, k, l, rfl⟩ := hg
  obtain ⟨i', j', k', l', rfl⟩ := hg'
  exact ⟨i + i', j + j', k + k', l + l', h.prod_mul i j k l i' j' k' l'⟩

theorem Inv4.exists_inv {a b c d : G} (h : Inv4 a b c d) {g : G}
    (hg : ∃ i j k l : ℕ, g = a ^ i * b ^ j * c ^ k * d ^ l) :
    ∃ i j k l : ℕ, g⁻¹ = a ^ i * b ^ j * c ^ k * d ^ l := by
  obtain ⟨i, j, k, l, rfl⟩ := hg
  exact ⟨i, j, k, l, inv_eq_of_mul_eq_one_right (h.prod_sq i j k l)⟩

theorem Inv4.isElemAbelian {a b c d : G} (h : Inv4 a b c d) {H : Subgroup G}
    (hH : ∀ g : G, g ∈ H ↔ ∃ i j k l : ℕ, g = a ^ i * b ^ j * c ^ k * d ^ l) :
    Open.IsElemAbelian 2 H := by
  rw [isElemAbelian_iff]
  constructor
  · intro g hg g' hg'
    obtain ⟨i, j, k, l, rfl⟩ := (hH g).mp hg
    obtain ⟨i', j', k', l', rfl⟩ := (hH g').mp hg'
    rw [h.prod_mul, h.prod_mul, add_comm i, add_comm j, add_comm k, add_comm l]
  · intro g hg
    obtain ⟨i, j, k, l, rfl⟩ := (hH g).mp hg
    rw [sq]
    exact h.prod_sq i j k l

theorem card_sup_zpowers_two {H : Subgroup G} {y : G} (hy2 : y ^ 2 = 1) (hyH : y ∉ H)
    (hc : ∀ h ∈ H, h * y = y * h) : Nat.card ↥(H ⊔ zpowers y) = Nat.card ↥H * 2 := by
  have hcomm : ∀ a ∈ H, ∀ b ∈ zpowers y, a * b = b * a := by
    intro a ha b hb
    rcases mem_zpowers_of_sq hy2 hb with h | h
    · rw [h]; simp
    · rw [h]; exact hc a ha
  have hinf : H ⊓ zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rcases mem_zpowers_of_sq hy2 hg.2 with h | h
    · rw [h]; exact Subgroup.one_mem _
    · exact absurd (h ▸ hg.1) hyH
  have hy1 : y ≠ 1 := fun h => hyH (h ▸ H.one_mem)
  rw [card_sup_of_commute hcomm hinf, card_zpowers_two hy2 hy1]

theorem eq_sup4 {a b c d : G} {H : Subgroup G}
    (hH : ∀ g : G, g ∈ H ↔ ∃ i j k l : ℕ, g = a ^ i * b ^ j * c ^ k * d ^ l) :
    H = zpowers a ⊔ zpowers b ⊔ zpowers c ⊔ zpowers d := by
  apply le_antisymm
  · intro g hg
    obtain ⟨i, j, k, l, rfl⟩ := (hH g).mp hg
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) i)))
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) j)))
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) k))
    · exact Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers d) l)
  · refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_ <;> rw [Subgroup.zpowers_le] <;> rw [hH]
    · exact ⟨1, 0, 0, 0, by simp⟩
    · exact ⟨0, 1, 0, 0, by simp⟩
    · exact ⟨0, 0, 1, 0, by simp⟩
    · exact ⟨0, 0, 0, 1, by simp⟩

theorem conj_prod4 (w a b c d : G) (i j k l : ℕ) :
    w * (a ^ i * b ^ j * c ^ k * d ^ l) * w⁻¹ =
      (w * a * w⁻¹) ^ i * (w * b * w⁻¹) ^ j * (w * c * w⁻¹) ^ k * (w * d * w⁻¹) ^ l := by
  rw [conj_pow, conj_pow, conj_pow, conj_pow]; group

theorem no_twist {P : Subgroup G} {r s z : G} (d : IsD8 P r s z) {y : G} (hyr : y * r * y⁻¹ = r⁻¹)
    (hys : y * s * y⁻¹ = r * s ∨ y * s * y⁻¹ = r ^ 3 * s) (hyz : y * z * y⁻¹ = z)
    {p : G} (hp : p ∈ P) (hp2 : p ^ 2 = 1) (h : y * p * y⁻¹ * z = p) : False := by
  obtain ⟨ε, hε, hε13⟩ : ∃ ε : ℕ, y * s * y⁻¹ = r ^ ε * s ∧ (ε = 1 ∨ ε = 3) := by
    rcases hys with h' | h'
    · exact ⟨1, by rw [h', pow_one], Or.inl rfl⟩
    · exact ⟨3, h', Or.inr rfl⟩
  have hz : z = r ^ 2 := d.z_eq
  have hrefl : ∀ a : ℕ, p = r ^ a * s → False := by
    intro a ha
    have hyrk : y * r ^ a * y⁻¹ = (r⁻¹) ^ a := by rw [← hyr]; exact (conj_pow).symm
    have key : y * (r ^ a * s) * y⁻¹ = (r⁻¹) ^ a * (r ^ ε * s) := by
      rw [← hε, ← hyrk]; group
    rw [ha, key] at h
    have e1 : r ^ (2 * a) * s = r ^ (ε + 2) * s := by
      calc r ^ (2 * a) * s = r ^ a * (r ^ a * s) := by rw [two_mul, pow_add]; group
        _ = r ^ a * ((r⁻¹) ^ a * (r ^ ε * s) * z) := by rw [h]
        _ = r ^ ε * (s * z) := by group
        _ = r ^ ε * (z * s) := by rw [d.z_comm_s]
        _ = r ^ (ε + 2) * s := by rw [hz]; group
    have e2 : r ^ (2 * a) = r ^ (ε + 2) := mul_right_cancel e1
    rw [pow_eq_pow_mod _ d.r4, pow_eq_pow_mod (ε + 2) d.r4] at e2
    have h1 : (2 * a) % 4 = 0 ∨ (2 * a) % 4 = 2 := by omega
    have h2 : (ε + 2) % 4 = 3 ∨ (ε + 2) % 4 = 1 := by omega
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] at e2
    · exact d.r3_ne_one (by simpa using e2.symm)
    · exact d.r_ne_one (by simpa using e2.symm)
    · exact d.r3_ne_sq e2.symm
    · exact d.r_ne_sq (by simpa using e2.symm)
  rcases d.P_inv hp hp2 with h1 | h1 | h1 | h1 | h1 | h1
  · rw [h1] at h
    exact d.z_ne_one (by simpa using h)
  · rw [h1, hyz] at h
    exact d.z_ne_one (by simpa using h)
  · exact hrefl 0 (by rw [h1]; group)
  · exact hrefl 2 (by rw [h1, hz])
  · exact hrefl 1 (by rw [h1, pow_one])
  · exact hrefl 3 (by rw [h1, hz]; group)

end General

end E16Aux

section Main

variable {G : Type} [Group G] [Finite G] {T P Q : Subgroup G} {u z x f r s : G}

namespace E16Aux

theorem inv4_A (c : Cfg89T G T P Q u z x f r s) : Inv4 u f z s where
  ab := (c.u_central f c.f_mem).symm
  ac := (c.u_central z (c.P_le c.z_mem)).symm
  ad := (c.u_central s (c.P_le c.s_mem)).symm
  bc := c.f_cent z c.z_mem
  bd := c.f_cent s c.s_mem
  cd := c.z_comm_s
  a2 := c.u2
  b2 := c.f2
  c2 := c.z_sq
  d2 := c.s2

theorem inv4_B (c : Cfg89T G T P Q u z x f r s) : Inv4 u f z (r * s) where
  ab := (c.u_central f c.f_mem).symm
  ac := (c.u_central z (c.P_le c.z_mem)).symm
  ad := (c.u_central (r * s) (c.P_le (P.mul_mem c.r_mem c.s_mem))).symm
  bc := c.f_cent z c.z_mem
  bd := c.f_cent (r * s) (P.mul_mem c.r_mem c.s_mem)
  cd := c.z_comm_P (r * s) (P.mul_mem c.r_mem c.s_mem)
  a2 := c.u2
  b2 := c.f2
  c2 := c.z_sq
  d2 := c.rs_sq

theorem u_mem_T (c : Cfg89T G T P Q u z x f r s) : u ∈ T := c.Q_le c.u_mem

theorem z_mem_T (c : Cfg89T G T P Q u z x f r s) : z ∈ T := c.P_le c.z_mem

theorem s_mem_T (c : Cfg89T G T P Q u z x f r s) : s ∈ T := c.P_le c.s_mem

theorem rs_mem_P (c : Cfg89T G T P Q u z x f r s) : r * s ∈ P := P.mul_mem c.r_mem c.s_mem

theorem rs_mem_T (c : Cfg89T G T P Q u z x f r s) : r * s ∈ T := c.P_le (rs_mem_P c)

end E16Aux

open E16Aux

@[expose] def EA (c : Cfg89T G T P Q u z x f r s) : Subgroup G where
  carrier := {g | ∃ i j k l : ℕ, g = u ^ i * f ^ j * z ^ k * s ^ l}
  one_mem' := ⟨0, 0, 0, 0, by simp⟩
  mul_mem' := fun {_ _} hg hh => (inv4_A c).exists_mul hg hh
  inv_mem' := fun {_} hg => (inv4_A c).exists_inv hg

@[expose] def EB (c : Cfg89T G T P Q u z x f r s) : Subgroup G where
  carrier := {g | ∃ i j k l : ℕ, g = u ^ i * f ^ j * z ^ k * (r * s) ^ l}
  one_mem' := ⟨0, 0, 0, 0, by simp⟩
  mul_mem' := fun {_ _} hg hh => (inv4_B c).exists_mul hg hh
  inv_mem' := fun {_} hg => (inv4_B c).exists_inv hg

theorem mem_EA (c : Cfg89T G T P Q u z x f r s) {g : G} :
    g ∈ EA c ↔ ∃ i j k l : ℕ, g = u ^ i * f ^ j * z ^ k * s ^ l := Iff.rfl

theorem isElemAbelian_EA (c : Cfg89T G T P Q u z x f r s) : Open.IsElemAbelian 2 (EA c) :=
  (inv4_A c).isElemAbelian (fun _ => Iff.rfl)

theorem isElemAbelian_EB (c : Cfg89T G T P Q u z x f r s) : Open.IsElemAbelian 2 (EB c) :=
  (inv4_B c).isElemAbelian (fun _ => Iff.rfl)

theorem EA_le_T (c : Cfg89T G T P Q u z x f r s) : EA c ≤ T := by
  rintro _ ⟨i, j, k, l, rfl⟩
  exact T.mul_mem (T.mul_mem (T.mul_mem (T.pow_mem (u_mem_T c) i) (T.pow_mem c.f_mem j))
    (T.pow_mem (z_mem_T c) k)) (T.pow_mem (s_mem_T c) l)

theorem EB_le_T (c : Cfg89T G T P Q u z x f r s) : EB c ≤ T := by
  rintro _ ⟨i, j, k, l, rfl⟩
  exact T.mul_mem (T.mul_mem (T.mul_mem (T.pow_mem (u_mem_T c) i) (T.pow_mem c.f_mem j))
    (T.pow_mem (z_mem_T c) k)) (T.pow_mem (rs_mem_T c) l)

namespace E16Aux

theorem u_mem_EA (c : Cfg89T G T P Q u z x f r s) : u ∈ EA c := ⟨1, 0, 0, 0, by simp⟩

theorem f_mem_EA (c : Cfg89T G T P Q u z x f r s) : f ∈ EA c := ⟨0, 1, 0, 0, by simp⟩

theorem z_mem_EA (c : Cfg89T G T P Q u z x f r s) : z ∈ EA c := ⟨0, 0, 1, 0, by simp⟩

theorem s_mem_EA (c : Cfg89T G T P Q u z x f r s) : s ∈ EA c := ⟨0, 0, 0, 1, by simp⟩

theorem u_mem_EB (c : Cfg89T G T P Q u z x f r s) : u ∈ EB c := ⟨1, 0, 0, 0, by simp⟩

theorem f_mem_EB (c : Cfg89T G T P Q u z x f r s) : f ∈ EB c := ⟨0, 1, 0, 0, by simp⟩

theorem z_mem_EB (c : Cfg89T G T P Q u z x f r s) : z ∈ EB c := ⟨0, 0, 1, 0, by simp⟩

theorem rs_mem_EB (c : Cfg89T G T P Q u z x f r s) : r * s ∈ EB c := ⟨0, 0, 0, 1, by simp⟩

theorem EA_eq_sup (c : Cfg89T G T P Q u z x f r s) :
    EA c = zpowers u ⊔ zpowers f ⊔ zpowers z ⊔ zpowers s :=
  eq_sup4 (fun _ => Iff.rfl)

theorem EB_eq_sup (c : Cfg89T G T P Q u z x f r s) :
    EB c = zpowers u ⊔ zpowers f ⊔ zpowers z ⊔ zpowers (r * s) :=
  eq_sup4 (fun _ => Iff.rfl)

theorem z_not_mem_V1 (c : Cfg89T G T P Q u z x f r s) : z ∉ zpowers u ⊔ zpowers f := by
  intro hz
  have hcomm : ∀ a ∈ zpowers u, ∀ b ∈ zpowers f, a * b = b * a := by
    intro a ha b hb
    rcases mem_zpowers_of_sq c.u2 ha with h | h <;> rcases mem_zpowers_of_sq c.f2 hb with h' | h'
    · simp [h, h']
    · simp [h, h']
    · simp [h, h']
    · rw [h, h']; exact (inv4_A c).ab
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute hcomm hz
  have : z = 1 := by
    apply c.P_inf_Qf c.z_mem
    rcases mem_zpowers_of_sq c.u2 ha with h | h <;> rcases mem_zpowers_of_sq c.f2 hb with h' | h'
    · exact ⟨1, Q.one_mem, 0, by rw [← hab, h, h']; simp⟩
    · exact ⟨1, Q.one_mem, 1, by rw [← hab, h, h']; simp⟩
    · exact ⟨u, c.u_mem, 0, by rw [← hab, h, h']; simp⟩
    · exact ⟨u, c.u_mem, 1, by rw [← hab, h, h']; simp⟩
  exact c.z_ne_one this

theorem V2_le_cent (c : Cfg89T G T P Q u z x f r s) :
    zpowers u ⊔ zpowers f ⊔ zpowers z ≤ centralizer (P : Set G) := by
  refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le] <;>
    rw [Subgroup.mem_centralizer_iff] <;> intro p hp
  · exact c.PQ_comm p hp u c.u_mem
  · exact (c.f_cent p hp).symm
  · exact (c.z_comm_P p hp).symm

theorem not_mem_V2 (c : Cfg89T G T P Q u z x f r s) {y : G} (hyP : y ∈ P) (hy1 : y ≠ 1)
    (hyz : y ≠ z) : y ∉ zpowers u ⊔ zpowers f ⊔ zpowers z := by
  intro hy
  have h := Subgroup.mem_centralizer_iff.mp (V2_le_cent c hy)
  rcases c.P_center hyP (fun p' hp' => (h p' hp').symm) with h1 | h1
  · exact hy1 h1
  · exact hyz h1

theorem card_V1 (c : Cfg89T G T P Q u z x f r s) : Nat.card ↥(zpowers u ⊔ zpowers f) = 4 :=
  card_klein c.u2 c.f2 (inv4_A c).ab c.u_ne c.f_ne_one c.u_ne_f.symm

theorem card_V2 (c : Cfg89T G T P Q u z x f r s) :
    Nat.card ↥(zpowers u ⊔ zpowers f ⊔ zpowers z) = 8 := by
  have hcomm : ∀ h ∈ zpowers u ⊔ zpowers f, h * z = z * h := by
    intro h hh
    have hle : zpowers u ⊔ zpowers f ≤ centralizer ({z} : Set G) := by
      refine sup_le ?_ ?_ <;> rw [Subgroup.zpowers_le] <;>
        rw [Subgroup.mem_centralizer_singleton_iff]
      · exact (inv4_A c).ac
      · exact (inv4_A c).bc
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  rw [card_sup_zpowers_two c.z_sq (z_not_mem_V1 c) hcomm, card_V1 c]

end E16Aux

theorem card_EA (c : Cfg89T G T P Q u z x f r s) : Nat.card ↥(EA c) = 16 := by
  rw [EA_eq_sup c]
  have hcomm : ∀ h ∈ zpowers u ⊔ zpowers f ⊔ zpowers z, h * s = s * h := by
    intro h hh
    have hle : zpowers u ⊔ zpowers f ⊔ zpowers z ≤ centralizer ({s} : Set G) := by
      refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le] <;>
        rw [Subgroup.mem_centralizer_singleton_iff]
      · exact (inv4_A c).ad
      · exact (inv4_A c).bd
      · exact (inv4_A c).cd
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  rw [card_sup_zpowers_two c.s2 (not_mem_V2 c c.s_mem c.s_ne_one c.s_ne_z) hcomm, card_V2 c]

theorem card_EB (c : Cfg89T G T P Q u z x f r s) : Nat.card ↥(EB c) = 16 := by
  rw [EB_eq_sup c]
  have hcomm : ∀ h ∈ zpowers u ⊔ zpowers f ⊔ zpowers z, h * (r * s) = (r * s) * h := by
    intro h hh
    have hle : zpowers u ⊔ zpowers f ⊔ zpowers z ≤ centralizer ({r * s} : Set G) := by
      refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le] <;>
        rw [Subgroup.mem_centralizer_singleton_iff]
      · exact (inv4_B c).ad
      · exact (inv4_B c).bd
      · exact (inv4_B c).cd
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  rw [card_sup_zpowers_two c.rs_sq (not_mem_V2 c (rs_mem_P c) c.rs_ne_one c.rs_ne_z) hcomm,
    card_V2 c]

theorem EA_ne_EB (c : Cfg89T G T P Q u z x f r s) : EA c ≠ EB c := by
  intro h
  have hs : s ∈ EB c := h ▸ s_mem_EA c
  rw [EB_eq_sup] at hs
  have hcomm : ∀ a ∈ zpowers u ⊔ zpowers f ⊔ zpowers z, ∀ b ∈ zpowers (r * s), a * b = b * a := by
    intro a ha b hb
    have hle : zpowers u ⊔ zpowers f ⊔ zpowers z ≤ centralizer ({r * s} : Set G) := by
      refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le] <;>
        rw [Subgroup.mem_centralizer_singleton_iff]
      · exact (inv4_B c).ad
      · exact (inv4_B c).bd
      · exact (inv4_B c).cd
    have h1 : a * (r * s) = (r * s) * a := Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
    rcases mem_zpowers_of_sq c.rs_sq hb with h2 | h2
    · rw [h2]; simp
    · rw [h2]; exact h1
  have hs' : s ∈ (zpowers u ⊔ zpowers f ⊔ zpowers z) ⊔ zpowers (r * s) := by
    simpa only [sup_assoc] using hs
  obtain ⟨v, hv, b, hb, hvb⟩ := mem_sup_of_commute hcomm hs'
  rcases mem_zpowers_of_sq c.rs_sq hb with h2 | h2
  · rw [h2, mul_one] at hvb
    exact not_mem_V2 c c.s_mem c.s_ne_one c.s_ne_z (hvb ▸ hv)
  · rw [h2] at hvb
    have hv' : v = r⁻¹ := by
      calc v = (v * (r * s)) * s⁻¹ * r⁻¹ := by group
        _ = r⁻¹ := by rw [hvb]; group
    have hr : r ∈ zpowers u ⊔ zpowers f ⊔ zpowers z := by
      have := (zpowers u ⊔ zpowers f ⊔ zpowers z).inv_mem hv
      rwa [hv', inv_inv] at this
    exact not_mem_V2 c c.r_mem c.isD8.r_ne_one (fun h' => c.isD8.r_ne_sq (h'.trans c.z_eq)) hr

namespace E16Aux

theorem x_conj_u (c : Cfg89T G T P Q u z x f r s) : x * u * x⁻¹ = u := by
  calc x * u * x⁻¹ = u * x * x⁻¹ := by rw [c.u_central x c.x_mem]
    _ = u := by group

theorem x_conj_z (c : Cfg89T G T P Q u z x f r s) : x * z * x⁻¹ = z := by
  calc x * z * x⁻¹ = z * x * x⁻¹ := by rw [c.z_central x c.x_mem]
    _ = z := by group

theorem x_conj_conj (c : Cfg89T G T P Q u z x f r s) (w : G) : x * (x * w * x⁻¹) * x⁻¹ = w := by
  calc x * (x * w * x⁻¹) * x⁻¹ = x ^ 2 * w * (x ^ 2)⁻¹ := by rw [sq]; group
    _ = w := by rw [c.x2]; group

theorem r3_s_eq (c : Cfg89T G T P Q u z x f r s) : r ^ 3 * s = z * (r * s) := by
  rw [c.z_eq]; group

theorem x_conj_f_mem (c : Cfg89T G T P Q u z x f r s) (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u) :
    x * f * x⁻¹ ∈ EA c ∧ x * f * x⁻¹ ∈ EB c := by
  obtain ⟨q, hq, hxf⟩ := c.xf
  rw [hxf]
  rcases hQ' q hq with h | h
  · rw [h, mul_one]
    exact ⟨(EA c).mul_mem (z_mem_EA c) (f_mem_EA c), (EB c).mul_mem (z_mem_EB c) (f_mem_EB c)⟩
  · rw [h]
    exact ⟨(EA c).mul_mem ((EA c).mul_mem (z_mem_EA c) (u_mem_EA c)) (f_mem_EA c),
      (EB c).mul_mem ((EB c).mul_mem (z_mem_EB c) (u_mem_EB c)) (f_mem_EB c)⟩

theorem x_conj_s_mem (c : Cfg89T G T P Q u z x f r s) : x * s * x⁻¹ ∈ EB c := by
  rcases c.x_s with h | h
  · rw [h]; exact rs_mem_EB c
  · rw [h, r3_s_eq c]; exact (EB c).mul_mem (z_mem_EB c) (rs_mem_EB c)

theorem x_conj_rs_mem (c : Cfg89T G T P Q u z x f r s) : x * (r * s) * x⁻¹ ∈ EA c := by
  have e : x * (r * s) * x⁻¹ = (x * r * x⁻¹) * (x * s * x⁻¹) := by group
  rw [e, c.x_r]
  rcases c.x_s with h | h
  · rw [h]
    have : r⁻¹ * (r * s) = s := by group
    rw [this]; exact s_mem_EA c
  · rw [h]
    have : r⁻¹ * (r ^ 3 * s) = z * s := by rw [c.z_eq]; group
    rw [this]; exact (EA c).mul_mem (z_mem_EA c) (s_mem_EA c)

end E16Aux

theorem x_swap_EA (c : Cfg89T G T P Q u z x f r s) (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u) :
    ∀ g : G, g ∈ EB c ↔ ∃ h ∈ EA c, g = x * h * x⁻¹ := by
  intro g
  constructor
  · rintro ⟨i, j, k, l, rfl⟩
    refine ⟨x * (u ^ i * f ^ j * z ^ k * (r * s) ^ l) * x⁻¹, ?_, (x_conj_conj c _).symm⟩
    rw [conj_prod4, x_conj_u c, x_conj_z c]
    exact (EA c).mul_mem ((EA c).mul_mem ((EA c).mul_mem ((EA c).pow_mem (u_mem_EA c) i)
      ((EA c).pow_mem (x_conj_f_mem c hQ').1 j)) ((EA c).pow_mem (z_mem_EA c) k))
      ((EA c).pow_mem (x_conj_rs_mem c) l)
  · rintro ⟨h, ⟨i, j, k, l, rfl⟩, rfl⟩
    rw [conj_prod4, x_conj_u c, x_conj_z c]
    exact (EB c).mul_mem ((EB c).mul_mem ((EB c).mul_mem ((EB c).pow_mem (u_mem_EB c) i)
      ((EB c).pow_mem (x_conj_f_mem c hQ').2 j)) ((EB c).pow_mem (z_mem_EB c) k))
      ((EB c).pow_mem (x_conj_s_mem c) l)

theorem M0_eq_EA_sup_EB (c : Cfg89T G T P Q u z x f r s) (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u) :
    M0 c = EA c ⊔ EB c := by
  apply le_antisymm
  · rintro _ ⟨p, hp, q, hq, i, rfl⟩
    have hs : s ∈ EA c ⊔ EB c := Subgroup.mem_sup_left (s_mem_EA c)
    have hr : r ∈ EA c ⊔ EB c := by
      have h1 : (r * s) * s ∈ EA c ⊔ EB c :=
        (EA c ⊔ EB c).mul_mem (Subgroup.mem_sup_right (rs_mem_EB c)) hs
      have e : r * s * s = r := by rw [mul_assoc, ← sq, c.s2, mul_one]
      rwa [e] at h1
    have hp' : p ∈ EA c ⊔ EB c := by
      obtain ⟨a, b, rfl⟩ := c.P_gen p hp
      exact (EA c ⊔ EB c).mul_mem ((EA c ⊔ EB c).pow_mem hr a) ((EA c ⊔ EB c).pow_mem hs b)
    have hq' : q ∈ EA c ⊔ EB c := by
      rcases hQ' q hq with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_sup_left (u_mem_EA c)
    exact (EA c ⊔ EB c).mul_mem ((EA c ⊔ EB c).mul_mem hp' hq')
      ((EA c ⊔ EB c).pow_mem (Subgroup.mem_sup_left (f_mem_EA c)) i)
  · refine sup_le ?_ ?_
    · rintro _ ⟨i, j, k, l, rfl⟩
      exact (M0 c).mul_mem ((M0 c).mul_mem ((M0 c).mul_mem ((M0 c).pow_mem (Q_le_M0 c c.u_mem) i)
        ((M0 c).pow_mem (f_mem_M0 c) j)) ((M0 c).pow_mem (P_le_M0 c c.z_mem) k))
        ((M0 c).pow_mem (P_le_M0 c c.s_mem) l)
    · rintro _ ⟨i, j, k, l, rfl⟩
      exact (M0 c).mul_mem ((M0 c).mul_mem ((M0 c).mul_mem ((M0 c).pow_mem (Q_le_M0 c c.u_mem) i)
        ((M0 c).pow_mem (f_mem_M0 c) j)) ((M0 c).pow_mem (P_le_M0 c c.z_mem) k))
        ((M0 c).pow_mem (P_le_M0 c (rs_mem_P c)) l)

namespace E16Aux

theorem not_inner_of_not_mem_M0 (c : Cfg89T G T P Q u z x f r s) {y : G} (hyT : y ∈ T)
    (hyM : y ∉ M0 c) : ¬ ∃ d' ∈ P, ∀ p ∈ P, y * p * y⁻¹ = d' * p * d'⁻¹ := by
  rintro ⟨d', hd', h⟩
  have hd'T : d' ∈ T := c.P_le hd'
  have hyc : ∀ p ∈ P, (d'⁻¹ * y) * p = p * (d'⁻¹ * y) := by
    intro p hp
    have h1 := h p hp
    calc (d'⁻¹ * y) * p = d'⁻¹ * (y * p * y⁻¹) * y := by group
      _ = d'⁻¹ * (d' * p * d'⁻¹) * y := by rw [h1]
      _ = p * (d'⁻¹ * y) := by group
  obtain ⟨i, q, hq, j, hij⟩ := c.CTP (d'⁻¹ * y) (T.mul_mem (T.inv_mem hd'T) hyT) hyc
  apply hyM
  have e : y = d' * (z ^ i * q * f ^ j) := by
    rw [← hij]; group
  rw [e]
  exact (M0 c).mul_mem (P_le_M0 c hd') ⟨z ^ i, P.pow_mem c.z_mem i, q, hq, j, rfl⟩

theorem M0_comm_f (c : Cfg89T G T P Q u z x f r s) (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u) {m : G}
    (hm : m ∈ M0 c) : m * f = f * m := by
  obtain ⟨p, hp, q, hq, i, rfl⟩ := hm
  have h1 : p * f = f * p := (c.f_cent p hp).symm
  have h2 : q * f = f * q := by
    rcases hQ' q hq with h | h
    · rw [h]; simp
    · rw [h]; exact (c.u_central f c.f_mem).symm
  have h3 : f ^ i * f = f * f ^ i := ((Commute.refl f).pow_left i).eq
  calc p * q * f ^ i * f = p * q * (f ^ i * f) := by group
    _ = p * q * (f * f ^ i) := by rw [h3]
    _ = p * (q * f) * f ^ i := by group
    _ = p * (f * q) * f ^ i := by rw [h2]
    _ = (p * f) * q * f ^ i := by group
    _ = (f * p) * q * f ^ i := by rw [h1]
    _ = f * (p * q * f ^ i) := by group

theorem y_conj_f (c : Cfg89T G T P Q u z x f r s) (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u) {y : G}
    (hyT : y ∈ T) (hyM : y ∉ M0 c) : ∃ q0 ∈ Q, y * f * y⁻¹ = z * q0 * f := by
  rcases T_cases c hyT with h | ⟨m, hm, hy⟩
  · exact absurd h hyM
  · obtain ⟨q0, hq0, hxf⟩ := c.xf
    refine ⟨q0, hq0, ?_⟩
    have hmf := M0_comm_f c hQ' hm
    have hmz : m * z = z * m := c.z_central m (M0_le_T c hm)
    have hmq : m * q0 = q0 * m := by
      rcases hQ' q0 hq0 with h | h
      · rw [h]; simp
      · rw [h]; exact c.u_central m (M0_le_T c hm)
    have hcomm : m * (z * q0 * f) = (z * q0 * f) * m := by
      calc m * (z * q0 * f) = (m * z) * q0 * f := by group
        _ = z * m * q0 * f := by rw [hmz]
        _ = z * (m * q0) * f := by group
        _ = z * (q0 * m) * f := by rw [hmq]
        _ = z * q0 * (m * f) := by group
        _ = z * q0 * (f * m) := by rw [hmf]
        _ = (z * q0 * f) * m := by group
    calc y * f * y⁻¹ = m * (x * f * x⁻¹) * m⁻¹ := by rw [hy]; group
      _ = m * (z * q0 * f) * m⁻¹ := by rw [hxf]
      _ = (z * q0 * f) * m * m⁻¹ := by rw [hcomm]
      _ = z * q0 * f := by group

theorem w_cases (c : Cfg89T G T P Q u z x f r s) (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u) {y : G}
    (hyT : y ∈ T) (hy2 : y ^ 2 = 1) (hyM : y ∉ M0 c) {w : G} (hw : w ∈ M0 c) (hw2 : w ^ 2 = 1)
    (hwy : w * y = y * w) : w = 1 ∨ w = u ∨ w = z ∨ w = u * z := by
  obtain ⟨hyr, hys⟩ := c.isD8.outer_shape hy2 (fun p hp => c.P_norm y hyT p hp)
    (not_inner_of_not_mem_M0 c hyT hyM)
  have hyz : y * z * y⁻¹ = z := by
    calc y * z * y⁻¹ = z * y * y⁻¹ := by rw [c.z_central y hyT]
      _ = z := by group
  obtain ⟨q0, hq0, hyf⟩ := y_conj_f c hQ' hyT hyM
  obtain ⟨p, hp, q, hq, j, hwe, hp2, -⟩ := c.involution_M0_data hw hw2
  have hqc : ∀ t ∈ T, t * q = q * t := by
    intro t ht
    rcases hQ' q hq with h | h
    · rw [h]; simp
    · rw [h]; exact c.u_central t ht
  have hq0c : ∀ t ∈ T, t * q0 = q0 * t := by
    intro t ht
    rcases hQ' q0 hq0 with h | h
    · rw [h]; simp
    · rw [h]; exact c.u_central t ht
  have hzT : z ∈ T := z_mem_T c
  have hq0T : q0 ∈ T := c.Q_le hq0
  have hyq : y * q * y⁻¹ = q := by
    calc y * q * y⁻¹ = q * y * y⁻¹ := by rw [(hqc y hyT).symm]
      _ = q := by group
  have haP : y * p * y⁻¹ ∈ P := c.P_norm y hyT p hp
  set a := y * p * y⁻¹ with _ha
  have hyw : y * w * y⁻¹ = w := by
    calc y * w * y⁻¹ = w * y * y⁻¹ := by rw [hwy]
      _ = w := by group
  have hzq0 : (z * q0) * f = f * (z * q0) := by
    have h1 : z * f = f * z := (c.f_cent z c.z_mem).symm
    have h2 : q0 * f = f * q0 := by
      rcases hQ' q0 hq0 with h | h
      · rw [h]; simp
      · rw [h]; exact (c.u_central f c.f_mem).symm
    calc z * q0 * f = z * (q0 * f) := by group
      _ = z * (f * q0) := by rw [h2]
      _ = (z * f) * q0 := by group
      _ = (f * z) * q0 := by rw [h1]
      _ = f * (z * q0) := by group
  have hzq : z * q0 = q0 * z := hq0c z hzT
  have hfj : (z * q0 * f) ^ j = z ^ j * q0 ^ j * f ^ j := by
    rw [(show Commute (z * q0) f from hzq0).mul_pow, (show Commute z q0 from hzq).mul_pow]
  have hexp : y * w * y⁻¹ = a * (q * (z ^ j * q0 ^ j * f ^ j)) := by
    rw [hwe]
    calc y * (p * (q * f ^ j)) * y⁻¹
        = (y * p * y⁻¹) * ((y * q * y⁻¹) * (y * f * y⁻¹) ^ j) := by
          rw [conj_pow]; group
      _ = a * (q * (z ^ j * q0 ^ j * f ^ j)) := by rw [hyq, hyf, hfj]
  have hZT : z ^ j * q0 ^ j ∈ T := T.mul_mem (T.pow_mem hzT j) (T.pow_mem hq0T j)
  have hmain : a * (z ^ j * q0 ^ j) = p := by
    have e1 : a * (z ^ j * q0 ^ j) * (q * f ^ j) = p * (q * f ^ j) := by
      calc a * (z ^ j * q0 ^ j) * (q * f ^ j)
          = a * ((z ^ j * q0 ^ j) * q) * f ^ j := by group
        _ = a * (q * (z ^ j * q0 ^ j)) * f ^ j := by rw [hqc _ hZT]
        _ = a * (q * (z ^ j * q0 ^ j * f ^ j)) := by group
        _ = y * w * y⁻¹ := hexp.symm
        _ = w := hyw
        _ = p * (q * f ^ j) := hwe
    exact mul_right_cancel e1
  have hq0j : q0 ^ j = 1 := by
    apply c.PQ_inf
    · have e : q0 ^ j = (a * z ^ j)⁻¹ * p := by
        calc q0 ^ j = (a * z ^ j)⁻¹ * (a * (z ^ j * q0 ^ j)) := by group
          _ = (a * z ^ j)⁻¹ * p := by rw [hmain]
      rw [e]
      exact P.mul_mem (P.inv_mem (P.mul_mem haP (P.pow_mem c.z_mem j))) hp
    · exact Q.pow_mem hq0 j
  rw [hq0j, mul_one] at hmain
  rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hzj : z ^ j = 1 := by rw [hk, ← two_mul, pow_mul, c.z_sq, one_pow]
    have hfj1 : f ^ j = 1 := by rw [hk, ← two_mul, pow_mul, c.f2, one_pow]
    rw [hzj, mul_one] at hmain
    have hcent : y * p * y⁻¹ = p := hmain
    have hp1 : p = 1 ∨ p = z := c.isD8.cent_of_outer hyr hys hp hcent
    rw [hwe, hfj1, mul_one]
    rcases hQ' q hq with h | h <;> rcases hp1 with h' | h'
    · left; rw [h, h']; simp
    · right; right; left; rw [h, h']; simp
    · right; left; rw [h, h']; simp
    · right; right; right; rw [h, h']; exact c.u_central z hzT
  · exfalso
    have hzj : z ^ j = z := by rw [hk, pow_succ, pow_mul, c.z_sq, one_pow, one_mul]
    rw [hzj] at hmain
    exact no_twist c.isD8 hyr hys hyz hp hp2 hmain

theorem E16_le_M0 (c : Cfg89T G T P Q u z x f r s) (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u)
    {E : Subgroup G} (hE : E ≤ T) (hel : Open.IsElemAbelian 2 E) (hcard : Nat.card ↥E = 16) :
    E ≤ M0 c := by
  classical
  by_contra hne
  obtain ⟨y, hyE, hyM⟩ := IsConcreteLE.not_le_iff_exists.mp hne
  have hyT : y ∈ T := hE hyE
  have hcomm := (isElemAbelian_iff.mp hel).1
  have hsq := (isElemAbelian_iff.mp hel).2
  have hy2 : y ^ 2 = 1 := hsq y hyE
  obtain ⟨my, hmy, hyx⟩ : ∃ m ∈ M0 c, y = m * x := by
    rcases T_cases c hyT with h | h
    · exact absurd h hyM
    · exact h
  have hmemS : ∀ e ∈ E, e ∈ ({1, u, z, u * z} : Finset G) ∪
      ({1, u, z, u * z} : Finset G).image (fun d => d * y) := by
    intro e he
    have heT : e ∈ T := hE he
    rw [Finset.mem_union, Finset.mem_image]
    rcases T_cases c heT with h | ⟨m, hm, hex⟩
    · left
      have := w_cases c hQ' hyT hy2 hyM h (hsq e he) (hcomm e he y hyE)
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    · right
      have hmem : e * y⁻¹ ∈ M0 c := by
        have e1 : e * y⁻¹ = m * my⁻¹ := by rw [hex, hyx]; group
        rw [e1]; exact (M0 c).mul_mem hm ((M0 c).inv_mem hmy)
      have heE : e * y⁻¹ ∈ E := E.mul_mem he (E.inv_mem hyE)
      have := w_cases c hQ' hyT hy2 hyM hmem (hsq _ heE) (hcomm _ heE y hyE)
      refine ⟨e * y⁻¹, ?_, by group⟩
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  have hle : Nat.card ↥E ≤ 8 := by
    calc Nat.card ↥E = (E : Set G).ncard := Nat.card_coe_set_eq (E : Set G)
      _ ≤ (↑(({1, u, z, u * z} : Finset G) ∪
            ({1, u, z, u * z} : Finset G).image (fun d => d * y)) : Set G).ncard :=
          Set.ncard_le_ncard (fun e he => Finset.mem_coe.mpr (hmemS e he)) (Finset.finite_toSet _)
      _ = (({1, u, z, u * z} : Finset G) ∪
            ({1, u, z, u * z} : Finset G).image (fun d => d * y)).card := Set.ncard_coe_finset _
      _ ≤ ({1, u, z, u * z} : Finset G).card +
            (({1, u, z, u * z} : Finset G).image (fun d => d * y)).card :=
          Finset.card_union_le _ _
      _ ≤ 4 + 4 :=
          Nat.add_le_add Finset.card_le_four (le_trans Finset.card_image_le Finset.card_le_four)
  omega

theorem inv_M0_cases (c : Cfg89T G T P Q u z x f r s) (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u) {e : G}
    (he : e ∈ M0 c) (he2 : e ^ 2 = 1) :
    ∃ (p : G) (i j : ℕ), e = p * (u ^ i * f ^ j) ∧
      (p = 1 ∨ p = z ∨ p = s ∨ p = z * s ∨ p = r * s ∨ p = z * (r * s)) := by
  obtain ⟨p, hp, q, hq, j, hwe, hp2, -⟩ := c.involution_M0_data he he2
  rcases hQ' q hq with h | h
  · exact ⟨p, 0, j, by rw [hwe, h]; simp, c.P_inv hp hp2⟩
  · exact ⟨p, 1, j, by rw [hwe, h]; simp, c.P_inv hp hp2⟩

theorem v_comm_P (c : Cfg89T G T P Q u z x f r s) (i j : ℕ) {p : G} (hp : p ∈ P) :
    (u ^ i * f ^ j) * p = p * (u ^ i * f ^ j) := by
  have h1 : u ^ i * p = p * u ^ i :=
    (show Commute u p from (c.PQ_comm p hp u c.u_mem).symm).pow_left i |>.eq
  have h2 : f ^ j * p = p * f ^ j := c.f_pow_comm_P j hp
  calc u ^ i * f ^ j * p = u ^ i * (f ^ j * p) := by group
    _ = u ^ i * (p * f ^ j) := by rw [h2]
    _ = (u ^ i * p) * f ^ j := by group
    _ = (p * u ^ i) * f ^ j := by rw [h1]
    _ = p * (u ^ i * f ^ j) := by group

theorem v_comm_v (c : Cfg89T G T P Q u z x f r s) (i j i' j' : ℕ) :
    (u ^ i * f ^ j) * (u ^ i' * f ^ j') = (u ^ i' * f ^ j') * (u ^ i * f ^ j) := by
  have huf : Commute u f := (inv4_A c).ab
  have : Commute (u ^ i * f ^ j) (u ^ i' * f ^ j') := by
    apply Commute.mul_left <;> apply Commute.mul_right
    · exact Commute.pow_pow_self u i i'
    · exact huf.pow_pow i j'
    · exact (huf.pow_pow i' j).symm
    · exact Commute.pow_pow_self f j j'
  exact this.eq

theorem v_mem_EA (c : Cfg89T G T P Q u z x f r s) (i j : ℕ) : u ^ i * f ^ j ∈ EA c :=
  (EA c).mul_mem ((EA c).pow_mem (u_mem_EA c) i) ((EA c).pow_mem (f_mem_EA c) j)

theorem v_mem_EB (c : Cfg89T G T P Q u z x f r s) (i j : ℕ) : u ^ i * f ^ j ∈ EB c :=
  (EB c).mul_mem ((EB c).pow_mem (u_mem_EB c) i) ((EB c).pow_mem (f_mem_EB c) j)

theorem rs_s_eq (c : Cfg89T G T P Q u z x f r s) : r * s * s = r := by
  rw [mul_assoc, ← sq, c.s2, mul_one]

theorem s_rs_eq (c : Cfg89T G T P Q u z x f r s) : s * (r * s) = r ^ 3 := by
  calc s * (r * s) = (s * r) * s := by group
    _ = (r ^ 3 * s) * s := by rw [c.s_r]
    _ = r ^ 3 * (s * s) := by group
    _ = r ^ 3 := by rw [← sq, c.s2, mul_one]

theorem refl_comm_false (c : Cfg89T G T P Q u z x f r s) {α β : G} (hα : α = 1 ∨ α = z)
    (hβ : β = 1 ∨ β = z) (h : (α * (r * s)) * (β * s) = (β * s) * (α * (r * s))) : False := by
  have hαP : ∀ p ∈ P, α * p = p * α := by
    intro p hp
    rcases hα with h' | h'
    · rw [h']; simp
    · rw [h']; exact c.z_comm_P p hp
  have hβP : ∀ p ∈ P, β * p = p * β := by
    intro p hp
    rcases hβ with h' | h'
    · rw [h']; simp
    · rw [h']; exact c.z_comm_P p hp
  have hαβ : α * β = β * α := by
    rcases hα with h1 | h1 <;> rcases hβ with h2 | h2
    · rw [h1, h2]
    · rw [h1, h2]; simp
    · rw [h1, h2]; simp
    · rw [h1, h2]
  have e1 : (α * (r * s)) * (β * s) = (α * β) * r := by
    calc (α * (r * s)) * (β * s) = α * ((r * s) * β) * s := by group
      _ = α * (β * (r * s)) * s := by rw [(hβP _ (rs_mem_P c)).symm]
      _ = (α * β) * ((r * s) * s) := by group
      _ = (α * β) * r := by rw [rs_s_eq c]
  have e2 : (β * s) * (α * (r * s)) = (α * β) * r ^ 3 := by
    calc (β * s) * (α * (r * s)) = β * (s * α) * (r * s) := by group
      _ = β * (α * s) * (r * s) := by rw [(hαP s c.s_mem).symm]
      _ = (β * α) * (s * (r * s)) := by group
      _ = (α * β) * (s * (r * s)) := by rw [hαβ]
      _ = (α * β) * r ^ 3 := by rw [s_rs_eq c]
  rw [e1, e2] at h
  have h3 : r = r ^ 3 := mul_left_cancel h
  apply c.r2_ne
  have h4 : r * 1 = r * r ^ 2 := by
    calc r * 1 = r := mul_one r
      _ = r ^ 3 := h3
      _ = r * r ^ 2 := by group
  exact (mul_left_cancel h4).symm

theorem E_le_EA_or_EB (c : Cfg89T G T P Q u z x f r s) (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u)
    {E : Subgroup G} (hEM : E ≤ M0 c) (hel : Open.IsElemAbelian 2 E) : E ≤ EA c ∨ E ≤ EB c := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hA, hB⟩ := hcon
  obtain ⟨e1, he1E, he1A⟩ := IsConcreteLE.not_le_iff_exists.mp hA
  obtain ⟨e2, he2E, he2B⟩ := IsConcreteLE.not_le_iff_exists.mp hB
  have hcomm := (isElemAbelian_iff.mp hel).1
  have hsq := (isElemAbelian_iff.mp hel).2
  obtain ⟨p1, i1, j1, he1, hp1⟩ := inv_M0_cases c hQ' (hEM he1E) (hsq e1 he1E)
  obtain ⟨p2, i2, j2, he2, hp2⟩ := inv_M0_cases c hQ' (hEM he2E) (hsq e2 he2E)
  have hp1' : p1 = r * s ∨ p1 = z * (r * s) := by
    rcases hp1 with h | h | h | h | h | h
    · exfalso; apply he1A; rw [he1, h, one_mul]; exact v_mem_EA c i1 j1
    · exfalso; apply he1A; rw [he1, h]; exact (EA c).mul_mem (z_mem_EA c) (v_mem_EA c i1 j1)
    · exfalso; apply he1A; rw [he1, h]; exact (EA c).mul_mem (s_mem_EA c) (v_mem_EA c i1 j1)
    · exfalso; apply he1A; rw [he1, h]
      exact (EA c).mul_mem ((EA c).mul_mem (z_mem_EA c) (s_mem_EA c)) (v_mem_EA c i1 j1)
    · exact Or.inl h
    · exact Or.inr h
  have hp2' : p2 = s ∨ p2 = z * s := by
    rcases hp2 with h | h | h | h | h | h
    · exfalso; apply he2B; rw [he2, h, one_mul]; exact v_mem_EB c i2 j2
    · exfalso; apply he2B; rw [he2, h]; exact (EB c).mul_mem (z_mem_EB c) (v_mem_EB c i2 j2)
    · exact Or.inl h
    · exact Or.inr h
    · exfalso; apply he2B; rw [he2, h]; exact (EB c).mul_mem (rs_mem_EB c) (v_mem_EB c i2 j2)
    · exfalso; apply he2B; rw [he2, h]
      exact (EB c).mul_mem ((EB c).mul_mem (z_mem_EB c) (rs_mem_EB c)) (v_mem_EB c i2 j2)
  have hp1P : p1 ∈ P := by
    rcases hp1' with h | h <;> rw [h]
    · exact rs_mem_P c
    · exact P.mul_mem c.z_mem (rs_mem_P c)
  have hp2P : p2 ∈ P := by
    rcases hp2' with h | h <;> rw [h]
    · exact c.s_mem
    · exact P.mul_mem c.z_mem c.s_mem
  have hee := hcomm e1 he1E e2 he2E
  have hpp : p1 * p2 = p2 * p1 := by
    have hv1 : (u ^ i1 * f ^ j1) * p2 = p2 * (u ^ i1 * f ^ j1) := v_comm_P c i1 j1 hp2P
    have hv2 : (u ^ i2 * f ^ j2) * p1 = p1 * (u ^ i2 * f ^ j2) := v_comm_P c i2 j2 hp1P
    have hvv := v_comm_v c i1 j1 i2 j2
    have l1 : e1 * e2 = p1 * p2 * ((u ^ i1 * f ^ j1) * (u ^ i2 * f ^ j2)) := by
      rw [he1, he2]
      calc p1 * (u ^ i1 * f ^ j1) * (p2 * (u ^ i2 * f ^ j2))
          = p1 * ((u ^ i1 * f ^ j1) * p2) * (u ^ i2 * f ^ j2) := by group
        _ = p1 * (p2 * (u ^ i1 * f ^ j1)) * (u ^ i2 * f ^ j2) := by rw [hv1]
        _ = p1 * p2 * ((u ^ i1 * f ^ j1) * (u ^ i2 * f ^ j2)) := by group
    have l2 : e2 * e1 = p2 * p1 * ((u ^ i1 * f ^ j1) * (u ^ i2 * f ^ j2)) := by
      rw [he1, he2]
      calc p2 * (u ^ i2 * f ^ j2) * (p1 * (u ^ i1 * f ^ j1))
          = p2 * ((u ^ i2 * f ^ j2) * p1) * (u ^ i1 * f ^ j1) := by group
        _ = p2 * (p1 * (u ^ i2 * f ^ j2)) * (u ^ i1 * f ^ j1) := by rw [hv2]
        _ = p2 * p1 * ((u ^ i2 * f ^ j2) * (u ^ i1 * f ^ j1)) := by group
        _ = p2 * p1 * ((u ^ i1 * f ^ j1) * (u ^ i2 * f ^ j2)) := by rw [hvv]
    rw [l1, l2] at hee
    exact mul_right_cancel hee
  rcases hp1' with h1 | h1 <;> rcases hp2' with h2 | h2
  · exact refl_comm_false c (α := 1) (β := 1) (Or.inl rfl) (Or.inl rfl) (by
      rw [h1, h2] at hpp; simpa using hpp)
  · exact refl_comm_false c (α := 1) (β := z) (Or.inl rfl) (Or.inr rfl) (by
      rw [h1, h2] at hpp; simpa using hpp)
  · exact refl_comm_false c (α := z) (β := 1) (Or.inr rfl) (Or.inl rfl) (by
      rw [h1, h2] at hpp; simpa using hpp)
  · exact refl_comm_false c (α := z) (β := z) (Or.inr rfl) (Or.inr rfl) (by
      rw [h1, h2] at hpp; exact hpp)

end E16Aux

theorem E16_unique (c : Cfg89T G T P Q u z x f r s) (hQ' : ∀ q ∈ Q, q = 1 ∨ q = u)
    {E : Subgroup G} (hE : E ≤ T) (hel : Open.IsElemAbelian 2 E) (hcard : Nat.card ↥E = 16) :
    E = EA c ∨ E = EB c := by
  rcases E_le_EA_or_EB c hQ' (E16_le_M0 c hQ' hE hel hcard) hel with h | h
  · left
    exact Subgroup.eq_of_le_of_card_ge h (by rw [hcard, card_EA c])
  · right
    exact Subgroup.eq_of_le_of_card_ge h (by rw [hcard, card_EB c])

end Main

end CFSG.GH74.GLS.C3.Layer1.P89
